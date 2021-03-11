
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

data Term
  = AtmT Atom 
  | LamT (Named Term)
  | AppT Term Atom
  | PriT PrimOp (List Atom)
  | LZPT PrimOp (List Term)
  | LetT Term Term
  | RecT Int (List (Named Term)) Term
  | PrgT Int (List (Named Term)) Term
  | CasT Atom (List BranchT)
  deriving Show

data BranchT
  = BranchT (Named Con) Int Term
  | DefaultT Term
  deriving Show

transformAtom :: (Level -> Atom -> Atom) -> Level -> Term -> Term
transformAtom f = go where 
  { go level term = case term of
    { AtmT a        -> AtmT (f level a)
    ; LamT nt       -> LamT (nfmap (go (inc level)) nt)
    ; AppT t a      -> AppT (go level t) (f level a)
    ; PriT p as     -> PriT p (map (f  level) as)
    ; LZPT p ts     -> LZPT p (map (go level) ts)
    ; LetT t1 t2    -> LetT (go level t1) (go (inc level) t2)
    ; RecT n nts t  -> let { level' = plus level n } in RecT n (map (nfmap (go level')) nts) (go level' t)
    ; CasT a brs    -> CasT (f level a) (map (goBranch level) brs) }
  ; goBranch level branch = case branch of  
    { BranchT c n t -> BranchT c n (go (plus level n) t)
    ; DefaultT    t -> DefaultT    (go       level t   ) } }

termSize :: Term -> Int
termSize term = go term where 
  { goNamed named = case named of { Named _ tm -> go tm }
  ; go term = case term of
    { AtmT _       -> 1
    ; LamT nbody   -> inc (goNamed nbody)
    ; AppT tm v    -> inc (go tm)
    ; PriT _ _     -> 1
    ; LZPT _ ts    -> inc (sum (map go ts))
    ; LetT t1 t2   -> inc (plus (go t1) (go t2))
    ; RecT _ ls tm -> inc (plus (sum (map goNamed ls)) (go tm))
    ; CasT _ brs   -> inc (sum (map goBranch brs)) }
  ; goBranch br = case br of
    { DefaultT tm    -> go tm
    ; BranchT _ k tm -> plus k (go tm) } }

--------------------------------------------------------------------------------
