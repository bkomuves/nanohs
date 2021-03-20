
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

insertIfSmall :: Size -> Level -> Term -> InlineEnv -> InlineEnv
insertIfSmall limit level term scope = 
  let { this = ifte (gt (termSize term) limit) NoInline (Inline level term) } in Cons this scope 

addNoInlines :: Int -> InlineEnv -> InlineEnv
addNoInlines n env = ifte (le n 0) env (addNoInlines (dec n) (Cons NoInline env))

optimizeCorePrg :: CoreProgram -> CoreProgram
optimizeCorePrg prg = let { limit = 24 } in 
  (inlineCorePrg limit
  (inlineCorePrg limit
  (inlineCorePrg limit prg)))

inlineCorePrg :: Size -> CoreProgram -> CoreProgram
inlineCorePrg sizeLimit coreprg = case coreprg of { CorePrg prg mainTerm -> CorePrg (inlineProgram sizeLimit prg) mainTerm } 

inlineProgram :: Size -> Program Term -> Program Term
inlineProgram sizeLimit blocks = termToProgram (inlineLets sizeLimit (programToTerm blocks))

inlineLets :: Size -> Term -> Term
inlineLets sizeLimit term = go 0 Nil term where
  { goIdx name level env i = case index i env of { NoInline -> AtmT (VarA (Named name (IdxV i))) 
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
      ; LetT nt1 t2   -> let { nt1' = nfmap (\t -> betaReduceTerm level (go level env t)) nt1 
      -- ; LetT nt1 t2   -> let { nt1' = (nfmap (go level env) nt1) 
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
