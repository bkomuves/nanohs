
-- | Closure conversion

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Closure where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import PrimOps
-- import DataCon
-- import Syntax
import Core
import ScopeCheck

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "PrimOps.hs"    %-}
-- {-% include "DataCon.hs"    %-}
-- {-% include "Syntax.hs"     %-}
{-% include "Core.hs"       %-}
{-% include "ScopeCheck.hs" %-}

--------------------------------------------------------------------------------

-- pattern VarF nvar = AtmF (VarA nvar)
-- pattern ConF ncon = AtmF (ConA ncon)
-- pattern KstF lit  = AtmF (KstA lit )

-- | We lift all lambdas (and lets, and branch right hand sides) to top-level
data Lifted
  = AtmF Atom
  | AppF Lifted Atom
  | PriF PrimOp (List Atom  )
  | LZPF PrimOp (List Lifted)
  | CasF Atom (List BranchF)
  | LamF ClosureF
  | RecF Int (List (Named ClosureF)) Lifted
  | LetF ClosureF Lifted
  deriving Show

data BranchF
  = BranchF (Named Con) Int ClosureF
  | DefaultF ClosureF
  deriving Show

isDefaultF :: BranchF -> Bool
isDefaultF branch = case branch of { DefaultF _ -> True ; _ -> False }

hasDefaultF :: List BranchF -> Bool
hasDefaultF ls = case ls of { Nil -> False ; Cons x xs -> case isDefaultF x of { True -> True ; _ -> hasDefaultF xs }}

-- | When allocating a closure, we create a new local environment
-- by pruning the current environment. We also remember the number
-- of lambda arguments (0 = thunk)
data ClosureF = ClosureF ClosureBody (List Idx) Arity deriving Show

data ClosureBody
  = StaticBody Static
  | InlineBody Lifted
  deriving Show

closureIndex :: ClosureF -> Static
closureIndex c = case c of { ClosureF b _ _ -> case b of { StaticBody s -> s ; _ -> error "closureIndex" } }

-- | A static function is an arity (which is separated to environment
-- size + actual lambda arity) together with a lifted body
data StatFun = StatFun Arity Arity Lifted deriving Show

-- | A top-level definition is a name, a static index and a static function
data TopLev = TopLev (Named Static) StatFun deriving Show

recogLamsT :: Term -> Pair (List Name) Term
recogLamsT term = case term of
  { LamT namedBody -> case namedBody of { Named name body ->
      case recogLamsT body of { Pair names rhs -> Pair (Cons name names) rhs } }
  ; _              -> Pair Nil term }

-- recogAppsF :: Lifted -> Pair Lifted (List Lifted)
-- recogAppsF term = case term of
--   { AppF tm1 tm2 -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args tm2) }
--   ; _            -> Pair term Nil }

recogAppsF :: Lifted -> Pair Lifted (List Atom)
recogAppsF term = case term of
  { AppF tm1 v2  -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args v2) }
  ; _            -> Pair term Nil }

-- | Figure out the part of the environment used by a term.
-- Returns a set of /levels/
pruneEnvironment :: Level -> Level -> Term -> IntSet
pruneEnvironment boundary = go where
  { goAtom level atom = case atom of
    { VarA nvar -> goVar level (forgetName nvar)
    ; ConA _    -> setEmpty
    ; KstA _    -> setEmpty }
  ; goVar  level var = case var of { TopV _ -> setEmpty ; StrV _ -> setEmpty ;
      IdxV idx -> let { j = minus level (inc idx) } in ifte (lt j boundary) (setSingleton j) setEmpty }
  ; go level term = case term of
    { AtmT atom   -> goAtom level atom
    ; AppT t1 a2  -> setUnion (go level t1) (goAtom level a2)
    ; PriT _ args -> setUnions (map (goAtom level) args)
    ; LZPT _ args -> setUnions (map (go     level) args)
    ; LamT nbody  -> go (inc level) (forgetName nbody)
    ; RecT n ts t -> let { level' = plus level n }
                     in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; PrgT n ts t -> let { level' = level }
                     in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; LetT t1 t2  -> setUnion (go (inc level) t2) (go level t1)
    ; CasT v brs  -> setUnion (goAtom level v) (setUnions (map (goBranch level) brs)) }
  ; goBranch level branch = case branch of
    { BranchT _ n rhs -> go (plus level n) rhs
    ; DefaultT    rhs -> go       level    rhs } }

-- | The closure conversion monad. Note: the list is reverse order!
type ClosM a = State (List TopLev) a

-- | Take the head entry of top level lists, and add 1 to it's index
nextStatic :: ClosM Static
nextStatic = sbind sget (\list -> case list of { Nil -> sreturn 0 ; Cons toplev _ ->
  case toplev of { TopLev named _ -> case named of { Named name s -> sreturn (inc s) }}})

-- addTopLev :: TopLev -> ClosM Unit
-- addTopLev what = smodify (Cons what)

addStatFun :: Name -> StatFun -> ClosM Static
addStatFun name statfun =
  sbind nextStatic                                             (\statidx ->
  sbind (smodify (Cons (TopLev (Named name statidx) statfun))) (\_       -> sreturn statidx ))

-- | The closure environment maps original levels to pruned de Bruijn indices
-- relative to the boundary
type ClosEnv = Map Level Idx

-- | A multi-lambda
data LambdaT
  = LambdaT Int Term
  deriving Show

-- | Closure-converting a lambda results in 1) a closure allocation
-- and 2) a static function. The latter we just add to the list of
-- of compiled stuff
--
-- The name is just a name for the resulting top-level definition
-- (so debugging is easier), and the level is the level where the lambda
-- starts (the \"boundary\" level)
--
-- TODO: this has really bad complexity because it always traverses subterms
-- at each recursive calls; we should instead define subsitutions and compose
-- them...
lambdaToClosure :: Int -> Name -> Level -> LambdaT -> ClosM ClosureF
lambdaToClosure nstatic name boundary lambda = case lambda of { LambdaT nargs body ->
  let { newlevel = plus boundary nargs
      ; pruned   = pruneEnvironment boundary newlevel body
      ; npruned  = length pruned
      ; ntotal   = plus nargs npruned
      ; newstart = minus boundary npruned
      ; envtable = zip pruned (reverse (range npruned))
      ; pr_idxs  = map (\j -> minus boundary (inc j)) pruned
      ; replaceIdx1 level idx = let { j = minus level (inc idx) } in 
          ifte (ge j boundary) (idx) 
            (case mapLookup j envtable of
              { Nothing -> error "lambdaToClosure: fatal error: variable not in the pruned environment"
              ; Just m  -> plus (minus level boundary) m })
      -- flip argument order (including the environment!)
      ; replaceIdx level old = let { idx = replaceIdx1 level old ; j = minus level (inc idx ) } in
          ifte (ge j newlevel) idx (plus (minus level newlevel) (minus j newstart))
      ; replaceAtom level atom = case atom of 
          { VarA nvar -> case nvar of { Named name var -> case var of
            { IdxV idx -> VarA (Named name (IdxV (replaceIdx level idx))) 
            ; _        -> atom }}
          ; _ -> atom }
      ; body' = transformAtom replaceAtom newlevel body
      }
  in  sbind (closureConvert nstatic name boundary newlevel body') (\statbody ->
      sbind (addStatFun name (StatFun npruned nargs statbody))    (\statidx  ->
      sreturn (ClosureF (StaticBody statidx) pr_idxs nargs))) }
-- debug name (Triple (Triple boundary nargs pruned) body body') (


termToStaticClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToStaticClosure nstatic name level tm = case recogLamsT tm of { Pair args body -> 
  lambdaToClosure nstatic name level (LambdaT (length args) body) }

termToInlineClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToInlineClosure nstatic name level tm = 
  sbind (closureConvert nstatic name 0 level tm) (\lifted ->
  sreturn (ClosureF (InlineBody lifted) Nil 0))

doInlineClosure :: Term -> Bool
doInlineClosure tm = case tm of
  { LamT _     -> False
  ; AtmT _     -> True
  ; _          -> le (termSize tm) 128 }

termToClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToClosure nstatic name level term = ifte (doInlineClosure term) 
  (termToInlineClosure nstatic name level term) 
  (termToStaticClosure nstatic name level term)

-- | The (named) int list is the mapping from the source code top-level functions
-- to the generated code top-level functions
data LiftedProgram = LProgram 
  { _toplevs :: List TopLev
  , _indices :: List (Named Int)
  , _main    :: Pair Int Lifted }
  deriving Show 

coreProgramToLifted :: CoreProgram -> LiftedProgram
coreProgramToLifted coreprg = case coreprg of { CorePrg defins mainTerm -> let
  { nstatic = length defins  
  ; action1 = sforM defins (\defin -> case defin of { Defin name term -> sfmap (\i -> Named name (closureIndex i)) (termToStaticClosure nstatic name 0 term) })
  ; action2 = closureConvert nstatic nanoMainIs 0 0 mainTerm  
  ; action  = sliftA2 Pair action1 action2
  ; mainidx = fromJust (findIndex (\def -> stringEq nanoMainIs (definedName def)) defins) 
  } in case runState action Nil of { Pair toplist pair2 -> 
         case pair2 of { Pair idxlist mainlft -> LProgram (reverse toplist) idxlist (Pair mainidx mainlft) } } }

addPrefix :: Name -> Name -> Name
addPrefix prefix name = append3 prefix "/" name

closureConvert :: Int -> Name -> Level -> Level -> Term -> ClosM Lifted
closureConvert nstatic nameprefix boundary = go where
  { prefixed name = addPrefix nameprefix name
  -- ; goVar level idx = IdxV idx
  -- ; goAtom level atom = case atom of 
  --     { VarA named -> case named of { Named name var -> case var of
  --       { IdxV idx   -> VarA (Named name (goVar level idx)) 
  --       ; TopV top   -> VarA (Named name (TopV top)) }}
  --     ; ConA named -> ConA named
  --     ; KstA lit   -> KstA lit   }
  ; goAtom level atom = atom
  ; go level term = case term of
    { AtmT named    -> sreturn (AtmF (goAtom level named))
    ; AppT t1 a2    -> sliftA2 AppF (go level t1) (sreturn (goAtom level a2))
    ; PriT pri args -> sreturn (PriF pri  ( map  (goAtom level) args))
    ; LZPT pri args -> sfmap   (LZPF pri) (smapM (go     level) args)
    ; LamT _        -> case recogLamsT term of { Pair args body ->
                         sfmap LamF (lambdaToClosure nstatic (prefixed "lambda") level (LambdaT (length args) body)) }
    ; CasT v brs    -> sfmap (CasF (goAtom level v)) (smapM (goBranch level) brs)
    ; RecT n nts tm -> let { level' = plus level n }
                       in  sliftA2 (RecF n) (smapM (goRec1 level') nts) (go level' tm) 
    ; LetT tm body  -> sliftA2 LetF (termToClosure nstatic (prefixed "let") level tm) (go (inc level) body) } 
  ; goRec1 level named = case named of { Named name tm -> sfmap (Named name) (termToStaticClosure nstatic (prefixed name) level tm) }
  ; goBranch level br  = case br of
    { DefaultT        rhs -> sfmap (DefaultF       ) (termToClosure    nstatic (prefixed "default")      level            rhs ) 
    ; BranchT named n rhs -> sfmap (BranchF named n) (lambdaToClosure nstatic  (prefixed (nameOf named)) level (LambdaT n rhs))
    }}

--------------------------------------------------------------------------------
