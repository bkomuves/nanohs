
-- | Core language

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Core where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Types
import PrimOps

{-% include "Base.hs"     %-}
{-% include "Types.hs"    %-}
{-% include "PrimOps.hs"  %-}

--------------------------------------------------------------------------------
-- ** Terms

-- pattern VarT nvar = AtmT (VarA nvar)
-- pattern ConT ncon = AtmT (ConA ncon)
-- pattern KstT lit  = AtmT (KstA lit )

type LTerm = Located Term

data Term
  = AtmT Atom 
  | LamT (Named Term)
  | AppT Term Atom
  | PriT PrimOp (List Atom)
  | LZPT PrimOp (List Term)
  | LetT (Named Term) Term
  | RecT Int (List (Named Term)) Term
  | CasT LAtom (List BranchT)
  | MainT
  deriving Show

data BranchT
  = BranchT (Named Con) Int Term
  | DefaultT Term
  deriving Show
 
-- | A list of top-level terms and the main (index and term, even though it's redundant)
data CoreProgram 
  = CorePrg (Program Term) TopIdx Term
  deriving Show

--------------------------------------------------------------------------------

showAtom :: Atom -> String
showAtom a = prettyAtom a

showTerm :: Term -> String
showTerm term = case term of
  { AtmT atom       -> showAtom atom
  ; LamT nbody      -> case nbody of { Named name body -> concat [ "(" , singleton backslashC , name , " -> " , showTerm body , ")" ] }
  ; AppT t a        -> concat [ "(" , showTerm t , " " , showAtom a , ")" ]
  ; PriT pop args   -> case pop of { PrimOp _ p -> concat [ showPrim p , "(" , intercalate "," (map showAtom args) , ")" ]} 
  ; LZPT pop args   -> case pop of { PrimOp _ p -> concat [ showPrim p , "(" , intercalate "," (map showTerm args) , ")" ]}
  ; LetT nt  body   -> concat [ "[let " , showNamedTerm nt , " in " , showTerm body , "]" ]
  ; RecT _ nts body -> concat [ "letrec { " , intercalate " ; " (map showNamedTerm nts) , " } in " , showTerm body ]
  ; CasT la brs     -> concat [ "case " , showAtom (located la) , " of { " ,intercalate " ; " (map showBranchT brs) , " }" ]
  ; MainT           -> "<main>" }

showNamedTerm :: Named Term -> String
showNamedTerm nterm = case nterm of { Named n t -> append3 n " = " (showTerm t) }

showBranchT :: BranchT -> String
showBranchT branch = case branch of
  { BranchT ncon n rhs -> concat [ nameOf ncon , " " , intercalate " " (map (\i -> appendInt "a" i) (rangeFrom 1 n)) , " -> " , showTerm rhs ]
  ; DefaultT rhs -> append "_ -> " (showTerm rhs) }

--------------------------------------------------------------------------------

programToTerm :: Program Term -> Term
programToTerm blocks = go 0 blocks where
  { go k blocks = case blocks of { Nil -> MainT ; Cons this rest -> case this of 
      { Recursive    defins -> let { n = length defins ; k' = plus k n} in
                               RecT n (map (worker k') defins) (go      k' rest)
      ; NonRecursive defin  -> LetT   (     worker k   defin ) (go (inc k) rest) }}
  ; worker level0 defin = case defin of { Defin name term -> Named name (transformVars f level0 term) } where
     { f _level var = case var of { IdxV i -> IdxV i 
                                  ; LevV j -> LevV (plus level0 j) 
                                  ; TopV k -> LevV k 
                                  ; _      -> var }}}

-- | it's important to eliminate levels because they can point to top-level definitions...?
-- TODO: to be really correct, we should recognize top-level definitions...
termToProgram :: Term -> Program Term
termToProgram term = go 0 term where  
  { go k term = case term of
      { RecT n nts body -> let { k' = plus k n } in  
                           Cons (Recursive     (map (worker k') nts)) (go      k' body)
      ; LetT   nt  body -> Cons (NonRecursive  (     worker k   nt )) (go (inc k) body)
      ; MainT -> Nil }
  ; worker level0 named = case named of { Named name term -> Defin name (transformVars f level0 term) } where
      { f level var = case var of { IdxV i -> g level (minus level (inc i)) ; LevV j -> g level j ; _ -> var }
      ; g level jdx = ifte (lt jdx level0) (TopV jdx) (IdxV (minus level (inc jdx)))
      }}

findToplevelMain :: Term -> TopIdx
findToplevelMain term = go 0 term where
  { go k term = case term of 
    { RecT n _ body -> go (plus k n) body
    ; LetT  nt body -> ifte (stringEq (nameOf nt) "main") k (go (inc k) body)
    ; MainT         -> error "findToplevelMain: top level `main` not found" }}

--------------------------------------------------------------------------------

transformVars :: (Level -> Var -> Var) -> Level -> Term -> Term
transformVars f = transformAtoms g where { g level atom = case atom of
  { VarA nvar -> case nvar of { Named name var -> VarA (Named name (f level var)) } ; _ -> atom } }

transformAtoms :: (Level -> Atom -> Atom) -> Level -> Term -> Term
transformAtoms f = transformTerm worker where
  { worker level term = case term of
    { AtmT a        -> AtmT (f level a)
    ; AppT t a      -> AppT t (f level a)
    ; PriT p as     -> PriT p (map (f level) as)
    ; CasT a brs    -> CasT (lfmap (f level) a) brs 
    ; _             -> term } }

transformTerm :: (Level -> Term -> Term) -> Level -> Term -> Term
transformTerm f level term = go level term where 
  { go level term = case term of
    { AtmT a        -> f level (AtmT a)
    ; LamT nt       -> f level (LamT (nfmap (go (inc level)) nt))
    ; AppT t a      -> f level (AppT (go level t) a)
    ; PriT p as     -> f level (PriT p as)
    ; LZPT p ts     -> f level (LZPT p (map (go level) ts))
    ; LetT nt1 t2   -> f level (LetT (nfmap (go level) nt1) (go (inc level) t2))
    ; RecT n nts t  -> f level (let { level' = plus level n } in RecT n (map (nfmap (go level')) nts) (go level' t))
    ; CasT la brs   -> f level (CasT la (map (goBranch level) brs)) 
    ; MainT         -> f level MainT }
  ; goBranch level branch = case branch of  
    { BranchT c n t -> BranchT c n (go (plus level n) t)
    ; DefaultT    t -> DefaultT    (go       level    t) } }

--------------------------------------------------------------------------------

-- | Shift de Bruijn indices in variables. We /add/ the offset to the indices,
-- leaving levels unchanged.
shiftVarRight :: Int -> Var -> Var
shiftVarRight ofs var = case var of 
   { IdxV i -> IdxV (plus i ofs) 
   ; LevV j -> LevV j
   ; _      -> var } 

-- | Shift de Bruijn indices in atoms
shiftAtomRight :: Int -> Atom -> Atom
shiftAtomRight ofs atom = case atom of  { VarA namedVar -> VarA (nfmap (shiftVarRight ofs) namedVar) ; _ -> atom }

-- | The condition should returin @True@ \"outside the term\"
shiftVarConditional :: (Level -> Bool) -> Int -> Level -> Var -> Var
shiftVarConditional cond ofs level var = case var of 
   { IdxV i -> let { j = minus level (inc i) } in 
               ifte (cond j)     (IdxV (plus i ofs)) var
   ; LevV j -> ifte (cond j) var (LevV (plus j ofs)) 
   ; _      -> var } 

shiftTerm :: Level -> Level -> Term -> Term
shiftTerm oldlevel newlevel term = let { shift = minus newlevel oldlevel } in 
  transformVars (\level var -> shiftVarConditional (\j -> lt j oldlevel) shift level var) oldlevel term

--------------------------------------------------------------------------------

atomIndexToLevel :: Level -> Atom -> Atom
atomIndexToLevel level atom = case atom of { VarA nvar -> case nvar of { Named name var -> case var of
  { IdxV i -> VarA (Named name (LevV (minus level (inc i)))) ; _ -> atom }} ; _ -> atom }

atomLevelToIndex :: Level -> Atom -> Atom
atomLevelToIndex level atom = case atom of { VarA nvar -> case nvar of { Named name var -> case var of
  { LevV j -> VarA (Named name (IdxV (minus level (inc j)))) ; _ -> atom }} ; _ -> atom }

termIndicesToLevels :: Level -> Term -> Term
termIndicesToLevels level term = transformAtoms atomIndexToLevel level term 

termLevelsToIndices :: Level -> Term -> Term
termLevelsToIndices level term = transformAtoms atomLevelToIndex level term 

--------------------------------------------------------------------------------

termSize :: Term -> Size
termSize term = go term where 
  { goNamed named = case named of { Named _ tm -> go tm }
  ; go term = case term of
    { AtmT _       -> 1
    ; LamT nbody   -> inc (goNamed nbody)
    ; AppT tm v    -> inc (go tm)
    ; PriT _ _     -> 1
    ; LZPT _ ts    -> inc (sum (map go ts))
    ; LetT nt1 t2  -> inc (plus (goNamed nt1) (go t2))
    ; RecT _ ls tm -> inc (plus (sum (map goNamed ls)) (go tm))
    ; CasT _ brs   -> inc (sum (map goBranch brs)) }
  ; goBranch br = case br of
    { DefaultT tm    -> go tm
    ; BranchT _ k tm -> plus k (go tm) } }

--------------------------------------------------------------------------------
