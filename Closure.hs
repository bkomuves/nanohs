
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
-- ** Types

-- pattern VarF nvar = AtmF (VarA nvar)
-- pattern ConF ncon = AtmF (ConA ncon)
-- pattern KstF lit  = AtmF (KstA lit )

-- | We lift all lambdas (and lets, and branch right hand sides) to top-level.
-- Note: In @LetF@, the Bool is there to note whether the bound expression needs to
-- be evaluated immediately.
data Lifted
  = AtmF Atom
  | AppF Lifted Atom
  | PriF PrimOp (List Atom  )
  | LZPF PrimOp (List Lifted)
  | CasF LAtom (List BranchF)
  | LamF ClosureF
  | RecF Int (List (Named ClosureF)) Lifted
  | LetF Bool ClosureF Lifted
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
-- of remaining arguments (0 = thunk)
data ClosureF = ClosureF ClosureBody (List Level) Arity deriving Show

data ClosureBody
  = StaticBody Static
  | InlineBody Lifted
  deriving Show

closureIndex :: ClosureF -> Static
closureIndex c = case c of { ClosureF b _ _ -> case b of { StaticBody s -> s ; _ -> error "closureIndex" } }

closureArity :: ClosureF -> Arity
closureArity c = case c of { ClosureF _ _ a -> a }

closureEnv :: ClosureF -> List Level
closureEnv c = case c of { ClosureF _ e _ -> e }

closureEnvSize :: ClosureF -> Int
closureEnvSize c = case c of { ClosureF _ e _ -> length e }

-- | A static function is an arity (which is separated to environment
-- size + actual lambda arity) together with a lifted body
data StatFun = StatFun Arity Arity Lifted deriving Show

statFunTotalArity :: StatFun -> Int
statFunTotalArity sfun = case sfun of { StatFun envsize arity _lifted -> plus envsize arity }

-- | A top-level definition is a name, a static index and a static function
data TopLev = TopLev (Named Static) StatFun deriving Show

topLevTotalArity :: TopLev  -> Int
topLevTotalArity toplev = case toplev of { TopLev _nidx sfun -> statFunTotalArity sfun }

--------------------------------------------------------------------------------

recogLamsT :: Term -> Pair (List Name) Term
recogLamsT term = case term of
  { LamT namedBody -> case namedBody of { Named name body ->
      case recogLamsT body of { Pair names rhs -> Pair (Cons name names) rhs } }
  ; _              -> Pair Nil term }

recogAppsF :: Lifted -> Pair Lifted (List Atom)
recogAppsF term = case term of
  { AppF tm1 v2  -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args v2) }
  ; _            -> Pair term Nil }

-- recogLetsT :: Term -> Pair (List Term) Term
-- recogLetsT term = case term of
--   { LetT t1 t2   -> case recogLetsT t2 of { Pair ts body -> Pair (Cons t1 ts) body } 
--   ; _            -> Pair Nil term }

--------------------------------------------------------------------------------
-- ** Closure converting programs

-- | The (named) int list is the mapping from the source code top-level functions
-- to the generated code top-level functions
data LiftedProgram = LProgram 
  { _toplevs :: List TopLev
  , _indices :: List (Named Int)
  , _main    :: Pair Int Lifted }
  deriving Show 

coreProgramToLifted :: CoreProgram -> LiftedProgram
coreProgramToLifted coreprg = case coreprg of { CorePrg blocks _mainIdx mainTerm -> let
  { nstatic = length defins  
  ; defins  = forgetBlockStructure blocks
  ; action1 = sforM defins (\defin -> case defin of { Defin name term -> 
      sfmap (\i -> Named name (closureIndex i)) (termToStaticClosure name idSubs 0 term) })
  ; action2 = closureConvert nanoMainIs idSubs 0 mainTerm  
  ; action  = sliftA2 Pair action1 action2
  ; mainidx = case findIndex (\def -> stringEq nanoMainIs (definedName def)) defins of { Just i -> i ; Nothing -> error "main not found" }
  } in case runState action Nil of { Pair toplist pair2 -> 
         case pair2 of { Pair idxlist mainlft -> LProgram (reverse toplist) idxlist (Pair mainidx mainlft) } } }

--------------------------------------------------------------------------------
-- ** Subsitutions and pruning

-- | Partial subsitutions
type Subs = (Level -> Maybe Level)

idSubs :: Subs 
idSubs = \j -> ifte (lt j 0) Nothing (Just j)

composeSubs :: Subs -> Subs -> Subs
composeSubs subs1 subs2 = \j -> case subs1 j of { Nothing -> Nothing ; Just k -> subs2 k }

-- | Substitution which flips (reverses) the first @n@ things
flipSubs :: Int -> Subs
flipSubs n = \j -> ifte (lt j 0) Nothing (Just (ifte (lt j n) (minus n (inc j)) j))

-- | Apply a substitution
applySubs :: Subs -> Level -> Level
applySubs subs j = case subs j of { Just k -> k ; _ -> error "substitution: input not in domain" }

type PrunedEnv = List Level

pruningSubs :: Subs -> Level -> Level -> Term -> Pair PrunedEnv Subs
pruningSubs oldsubs boundary level term = Pair pruned subs where
  { pruned0  = pruneEnvironment boundary level term
  ; pruned   = map (applySubs oldsubs) pruned0
  ; npruned  = length pruned
  ; envtable = zip pruned (range npruned)
  ; subs j   = ifte (lt j boundary) (mapLookup (applySubs oldsubs j) envtable) 
                                    (Just (plus (minus j boundary) npruned))
  } 

-- | Figure out the part of the environment used by a term.
-- Returns a set of /levels/
pruneEnvironment :: Level -> Level -> Term -> IntSet
pruneEnvironment boundary level term = go level term where
  { goAtom level atom = case atom of
    { VarA nvar -> goVar level (forgetName nvar)
    ; ConA _    -> setEmpty
    ; KstA _    -> setEmpty }
  ; goVar level var = case var of 
      { IdxV idx  -> goLevel (minus level (inc idx))
      ; LevV jdx  -> goLevel jdx
      ; TopV _    -> setEmpty 
      ; StrV _    -> setEmpty } 
  ; goLevel j = ifte (lt j boundary) (setSingleton j) setEmpty 
  ; go level term = case term of
    { AtmT atom   -> goAtom level atom
    ; AppT t1 a2  -> setUnion (go level t1) (goAtom level a2)
    ; PriT _ args -> setUnions (map (goAtom level) args)
    ; LZPT _ args -> setUnions (map (go     level) args)
    ; LamT nbody  -> go (inc level) (forgetName nbody)
    ; RecT n ts t -> let { level' = plus level n } in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; LetT nt1 t2 -> setUnion (go level (forgetName nt1)) (go (inc level) t2)
    ; CasT v brs  -> setUnion (goAtom level (located v)) (setUnions (map (goBranch level) brs)) }
  ; goBranch level branch = case branch of
    { BranchT _ n rhs -> go (plus level n) rhs
    ; DefaultT    rhs -> go       level    rhs } }

--------------------------------------------------------------------------------
-- ** Closure conversion

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
lambdaToClosure :: Name -> Subs -> Level -> LambdaT -> ClosM ClosureF
lambdaToClosure name oldsubs boundary lambda = case lambda of { LambdaT nargs body -> 
  let { newlevel = plus boundary nargs } in 
    case pruningSubs oldsubs boundary newlevel body of { Pair prunedEnv newsubs ->
      let { npruned = length prunedEnv ; ntotal = plus npruned nargs 
          ; newsubs' = composeSubs newsubs (flipSubs ntotal) }
      in  sbind (closureConvert name newsubs' newlevel body)        (\statbody ->
          sbind (addStatFun name (StatFun npruned nargs statbody))  (\statidx  ->
          sreturn (ClosureF (StaticBody statidx) prunedEnv nargs)))  }}

termToStaticClosure :: Name -> Subs -> Level -> Term -> ClosM ClosureF
termToStaticClosure name subs level tm = case recogLamsT tm of { Pair args body -> 
  lambdaToClosure name subs level (LambdaT (length args) body) }

-- Note: we don't do environment pruning here (boundary = 0)
termToInlineClosure :: Name -> Subs -> Level -> Term -> ClosM ClosureF
termToInlineClosure name subs level tm = 
  sbind (closureConvert name subs level tm) (\lifted ->
  sreturn (ClosureF (InlineBody lifted) Nil 0))

-- | Whether to make a static function out of this closure
doInlineClosure :: Term -> Bool
doInlineClosure tm = case tm of
  { LamT _  -> False
  ; AtmT _  -> True
  ; _       -> le (termSize tm) 64 }  

-- | In let bindings, it can happen that we bind some computation.
-- Since on the stack there should be only values, in this case
-- we have to evaluate them. On the other hand, for example lambdas and 
-- atoms do not need to be evaluated.
needsToBeEvaluated :: Term -> Bool
needsToBeEvaluated tm = case tm of
  { LamT _        -> False 
  ; AtmT _        -> False
  ; LetT _   body -> needsToBeEvaluated body
  ; RecT _ _ body -> needsToBeEvaluated body
  ; _             -> True }

termToClosure :: Name -> Subs -> Level -> Term -> ClosM ClosureF
termToClosure name subs level term = ifte (doInlineClosure term) 
  (termToInlineClosure name subs level term) 
  (termToStaticClosure name subs level term)

addPrefix :: Name -> Name -> Name
addPrefix prefix name = append3 prefix "/" name

closureConvert :: Name -> Subs -> Level -> Term -> ClosM Lifted
closureConvert nameprefix subs level term = go level term where
  { prefixed name = addPrefix nameprefix name
    -- convert to de Bruijn levels from indices
  ; goLev        jdx  = LevV (applySubs subs                   jdx  )
  ; goIdx  level idx  = LevV (applySubs subs (minus level (inc idx)))
  ; goAtom level atom = case atom of 
      { VarA named -> case named of { Named name var -> case var of
         { IdxV idx -> VarA (Named name (goIdx level idx)) 
         ; LevV jdx -> VarA (Named name (goLev       jdx))
         ; _        -> atom } }
      ; _  -> atom }
  ; go level term = case term of
    { AtmT named    -> sreturn (AtmF (goAtom level named))
    ; AppT t1 a2    -> sliftA2 AppF (go level t1) (sreturn (goAtom level a2))
    ; PriT pri args -> sreturn (PriF pri  ( map  (goAtom level) args))
    ; LZPT pri args -> sfmap   (LZPF pri) (smapM (go     level) args)
    ; LamT _        -> case recogLamsT term of { Pair args body ->
                         sfmap LamF (lambdaToClosure (prefixed "lambda")  subs level (LambdaT (length args) body)) }
    ; CasT lv brs   -> sfmap (CasF (lfmap (goAtom level) lv)) (smapM (goBranch level) brs)
    ; RecT n nts tm -> let { level' = plus level n }
                       in  sliftA2 (RecF n) (smapM (goRec1 level') nts) (go level' tm) 
    ; LetT ntm body -> case ntm of { Named name tm -> sliftA2 (LetF (needsToBeEvaluated tm)) 
                         (termToClosure (prefixed name) subs level tm) (go (inc level) body) } }
  ; goRec1 level named = case named of { Named name tm -> 
      sfmap (Named name) (termToStaticClosure (prefixed name) subs level tm) }
  ; goBranch level br  = case br of
    { DefaultT        rhs -> sfmap (DefaultF       ) (termToClosure   (prefixed "default")      subs level            rhs ) 
    ; BranchT named n rhs -> sfmap (BranchF named n) (lambdaToClosure (prefixed (nameOf named)) subs level (LambdaT n rhs))
    }}

--------------------------------------------------------------------------------
