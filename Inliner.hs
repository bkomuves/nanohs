
-- | Inlining small functions

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Inliner where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import Core

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "Core.hs"       %-}

--------------------------------------------------------------------------------
-- ** Inliner

data InlineTm
  = NoInline
  | Inline Level Term
  deriving Show

type InlineEnv = List InlineTm

-- | temp debugging
data TermSize = TermSize Int Int deriving Show

-- | NB: we should never inline stuff which does computation!
isInlineableTerm :: Term -> Bool
isInlineableTerm term = case term of
  { LamT _   -> True
  ; AtmT _   -> True
  ; LetT _ t -> isInlineableTerm t
  ; _        -> False }
  
insertIfSmall :: Size -> Level -> Term -> InlineEnv -> InlineEnv
insertIfSmall limit level term scope = case isInlineableTerm term of
  { True  -> let { this = ifte (gt (termSize term) limit) NoInline (Inline level term) } in (Cons this scope)
  ; False -> Cons NoInline scope }

addNoInlines :: Int -> InlineEnv -> InlineEnv
addNoInlines n env = ifte (le n 0) env (addNoInlines (dec n) (Cons NoInline env))

optimizeCorePrg :: CoreProgram -> CoreProgram
optimizeCorePrg prg = let { limit = 24 } in 
  (inlineCorePrg limit (inlineCorePrg limit
  (inlineCorePrg limit (inlineCorePrg limit
  (inlineCorePrg limit (inlineCorePrg limit prg))))))

inlineCorePrg :: Size -> CoreProgram -> CoreProgram
inlineCorePrg sizeLimit coreprg = case coreprg of 
  { CorePrg blocks mainIdx mainTerm -> let 
     { bigterm'  = removeUnusedLets mainIdx (inlineLets sizeLimit (programToTerm blocks))
     ; mainIdx'  = findToplevelMain bigterm'
     ; blocks'   = termToProgram    bigterm'
     ; mainTerm' = AtmT (VarA (Named "$main" (TopV mainIdx')))
     } in CorePrg blocks' mainIdx' mainTerm' } 

inlineLets :: Size -> Term -> Term
inlineLets sizeLimit term = go 0 Nil term where
  { goIdx name level env i = let { what = index i env } in case what of 
      { NoInline -> AtmT (VarA (Named name (IdxV i))) 
      ; Inline ilevel iterm -> shiftTerm ilevel level iterm }
  ; goAtom level env atom = case atom of { VarA nvar -> case nvar of { Named name var -> case var of
      { LevV j   -> goIdx name level env (minus level (inc j)) 
      ; IdxV i   -> goIdx name level env i
      ; _        -> AtmT atom } } ; _ -> AtmT atom }
  ; go level env term = case term of
      { AtmT atom     -> goAtom level env atom
      ; LamT nt       -> LamT (nfmap (go (inc level) (Cons NoInline env)) nt)
      ; AppT t a      -> AppT (go level env t) a
      ; PriT p as     -> PriT p as
      ; LZPT p ts     -> LZPT p (map (go level env) ts)
      -- ; LetT nt1 t2   -> let { nt1' = (nfmap (go level env) nt1) 
      ; LetT nt1 t2   -> let { nt1' = nfmap (\t -> betaReduceTerm level (go level env t)) nt1 
                             ; env' = insertIfSmall sizeLimit level (forgetName nt1') env } 
                         in  LetT nt1' (go (inc level) env' t2)
      ; RecT n nts t  -> let { level' = plus level n ; env' = addNoInlines n env } 
                         in  RecT n (map (nfmap (go level' env')) nts) (go level' env' t)
      ; CasT la brs   -> CasT la (map (goBranch level env) brs) 
      ; MainT         -> MainT }
  ; goBranch level env branch = case branch of  
      { BranchT c n t -> BranchT c n (go (plus level n) (addNoInlines n env) t)
      ; DefaultT    t -> DefaultT    (go       level                    env  t) } }

--------------------------------------------------------------------------------

-- ex1 = LamT (Named "x" (
--         LetT (Named "p" (AtmT (KstA (IntL 666))))
--           (PriT (PrimOp 2 Plus) [ VarA (Named "p" (IdxV 0)) , KstA (IntL 1) ] )))
-- 
-- ex2 = LamT (Named "x" (
--         LetT (Named "p" (AtmT (KstA (IntL 666))))
--           (PriT (PrimOp 2 Plus) [ VarA (Named "x" (IdxV 1)) , KstA (IntL 1) ] )))

--------------------------------------------------------------------------------

-- | NB: we have to know the @main@, otherwise we would eliminate /everything/
removeUnusedLets :: TopIdx -> Term -> Term
removeUnusedLets mainIdx term = snd (go 0 term) where
  { 
 -- goLev :: Level ->  Name -> Level -> Pair IntSet (Named Var)
    goLev level name j = Pair (setSingleton j) (Named name (LevV j)) 
 -- goAtom :: Level -> Atom -> Pair IntSet Atom
  ; goAtom level atom = case atom of { VarA nvar -> case nvar of { Named name var -> case var of
      { LevV j   -> second VarA (goLev level name j)
      ; IdxV i   -> second VarA (goLev level name (minus level (inc i)))
      ; _        -> Pair setEmpty atom } } ; _ -> Pair setEmpty atom }
 -- go :: Level -> Term -> Pair IntSet Term
  ; go level term = 
                    -- debug "level" level (debug "term" term (debug_ "term'" (
                    case term of 
      { AtmT atom      -> second AtmT (goAtom level atom)
      ; LamT nt        -> case go (inc level) (forgetName nt) of { Pair set t' ->
                            Pair (setDelete level set) (LamT (Named (nameOf nt) t')) }
      ; AppT t a       -> case go     level t of { Pair set1 t' -> 
                          case goAtom level a of { Pair set2 a' -> Pair (setUnion set1 set2) (AppT t' a') }}
      ; PriT p as      -> let { pairs = map (goAtom level) as } in Pair (setUnions (map fst pairs)) (PriT p (map snd pairs)) 
      ; LZPT p ts      -> let { pairs = map (go     level) ts } in Pair (setUnions (map fst pairs)) (LZPT p (map snd pairs)) 
      ; LetT nt1 t2    -> case nt1 of { Named name t1 -> case go level t1 of { Pair free1 t1' ->
                          case go (inc level) t2 of { Pair free2 t2' -> ifte (setMember level free2)
                            (Pair (setUnion free1 (setDelete level free2)) (LetT (Named name t1') t2'))
                            (Pair free2 (shiftTerm (inc level) level t2')) }}}
      ; RecT n nts tm  -> let { level' = plus level n ;
                                pairs = map (\nt -> case nt of { Named named t -> case go level' t of 
                                  { Pair set t' -> Pair set (Named named t') }}) nts } 
                          in  case go level' tm of { Pair set tm' ->
                                Pair (setUnion set (setDeleteMany (rangeFrom level n) (setUnions (map fst pairs)))) 
                                     (RecT n (map snd pairs) tm') }
      ; CasT la brs    -> case la of { Located loc a -> case goAtom level a of { Pair set1 a' -> 
                          let { pairs = map (goBranch level) brs } 
                          in  Pair (setUnion set1 (setUnions (map fst pairs))) (CasT (Located loc a') (map snd pairs)) }} 
      ; MainT          -> Pair (setSingleton mainIdx) MainT } 
                           -- (AtmT (VarA (Named "$main" (LevV mainIdx)))) } )))
 -- goBranch :: Level -> BranchT -> Pair IntSet BranchT
  ; goBranch level branch = case branch of
      { DefaultT rhs    -> case go level rhs of { Pair set rhs' -> Pair set (DefaultT rhs') }
      ; BranchT c n rhs -> let { level' = plus level n } in case go level' rhs of { Pair set rhs' -> 
                             let { set' = setDeleteMany (rangeFrom level n) set } in Pair set' (BranchT c n rhs') }} }

--------------------------------------------------------------------------------
-- ** Beta reduction

--_id    = LamT (Named "a" ( AtmT (VarA (Named "a" (IdxV 0)))))
--_const = LamT (Named "x" (
--         LamT (Named "y" ( AtmT (VarA (Named "x" (IdxV 1)))))))
--_kst5 = (KstA (IntL 5))
--_kst8 = (KstA (IntL 8))
--_idx0 = VarA (Named "$0" (IdxV 0))
--_idx1 = VarA (Named "$1" (IdxV 1))
--_idx2 = VarA (Named "$2" (IdxV 2))
--app1  f x    = AppT f x
--app2 f x y = AppT (AppT f x) y

betaReduceTerm :: Level -> Term -> Term
betaReduceTerm level term = transformTerm worker level term where
  { worker level term = case term of { AppT f arg -> case f of { LamT nbody -> case nbody of { Named name body -> 
      let { arg'  = atomIndexToLevel level arg
          ; body' = transformAtoms (substitute1 level arg') (inc level) body 
          ; final = shiftTerm (inc level) level body' }
      in  final
           -- debug "=========================" Unit (
           -- debug "level" level( 
           -- debug "f/arg" (Pair (showTerm f) (showAtom arg)) (
           -- debug "body"  (showTerm body)  (
           -- debug "arg'"  (showAtom arg' ) (
           -- debug "body'" (showTerm body') (
           -- debug "final" (showTerm final)  
           --  final))))))
           } ; _ -> term } ; _ -> term }
  ; substitute1 level0 what level atom =  
      let { handleLev name j = ifte (eq j level0) what (VarA (Named name (LevV j))) }
      in  case atom of { VarA nvar -> case nvar of { Named name var -> case var of 
            { IdxV i -> handleLev name (minus level (inc i))
            ; LevV j -> handleLev name j
            ; _ -> atom }} ; _ -> atom } }

--------------------------------------------------------------------------------
