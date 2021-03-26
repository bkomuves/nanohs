
-- | Scope checking and conversion to core

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module ScopeCheck where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import PrimOps
import DataCon
import Syntax
import Core

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "PrimOps.hs"    %-}
{-% include "DataCon.hs"    %-}
{-% include "Syntax.hs"     %-}
{-% include "Core.hs"       %-}

--------------------------------------------------------------------------------
-- * Config

-- | Name of the entry point
nanoMainIs :: Name
nanoMainIs = "main"

--------------------------------------------------------------------------------
-- * conversion to core
   
exprToCore :: Trie PrimOp -> DataConTable -> Scope -> Expr -> Term
exprToCore primops dconTable iniScope expr = scopeCheck dconTable iniScope (recogPrimApps1 primops expr)

programToCoreProgram :: Mode -> DataConTable -> Program Expr -> CoreProgram
programToCoreProgram mode dconTable blocks = CorePrg (map worker blocks) mainIdx mainTerm where
  { primops      = thePrimOps mode
  ; duplicate n  = concat [ "multiple declaration of " , quoteString n ]
  ; defins_      = map located (forgetBlockStructure blocks)
  ; topLevScope  = trieFromListUnique duplicate (zipWithIndex (\n i -> Pair n (TopL i)) (map definedName defins_))
  ; worker block = case block of 
      { NonRecursive defin  -> NonRecursive (     fmapLDefin (exprToCore primops dconTable topLevScope)  defin )
      ; Recursive    defins -> Recursive    (map (fmapLDefin (exprToCore primops dconTable topLevScope)) defins) }
  ; no_main_err = \_ -> error (concat [ "entry point " , quoteString nanoMainIs , " not found" ]) 
  ; mainIdx = case trieLookup nanoMainIs topLevScope of { Just varl -> case varl of
      { TopL k -> k ; _ -> no_main_err Unit } ; _ -> no_main_err Unit }  
  ; mainTerm = AtmT (VarA (Named nanoMainIs (TopV mainIdx))) }

--------------------------------------------------------------------------------
-- ** Scope checking

data VarL 
  = LevL Level 
  | TopL Int
  deriving Show

type Scope = Trie VarL

lookupVar :: Level -> Scope -> Location -> String -> Var
lookupVar level scope loc name =
  case trieLookup name scope of 
    { Just v  -> case v of { LevL k -> IdxV (dec (minus level k)) ; TopL j -> TopV j } 
    ; Nothing -> error (concat [ "variable name " , quoteString name , " not in scope, at " , showLocation loc ])}

lookupCon :: DataConTable -> String -> Con
lookupCon dcontable name =
  case trieLookup name dcontable of { Just con -> con ; Nothing ->
    error (concat [ "fatal error: constructor " , quoteString name , " not found" ])}

scopeCheck :: DataConTable -> Scope -> Expr -> Term
scopeCheck dcontable = go 0 where
  { mbAtom level scope expr =  case expr of
      { VarE  lname -> case lname of { Located loc name -> case isDCon name of
        { True  -> Just (ConA (Named name (lookupCon dcontable       name)))
        ; False -> Just (VarA (Named name (lookupVar level scope loc name))) }}
      ; LitE  lit -> case lit of
        { StrL cs -> Nothing
        ; _       -> Just (KstA lit) }
      ; _ -> Nothing } 
  ; go level scope expr = case expr of
    { VarE  name -> case mbAtom level scope expr of
        { Just atom -> AtmT atom
        ; Nothing   -> error "fatal error: VarE should be always an atom!" }
    ; StrE j     -> AtmT (VarA (Named (appendInt "str_" j) (StrV j)))
    ; AppE e1 e2 -> case mbAtom level scope e2 of
        { Just atom -> AppT (go level scope e1) atom
        ; Nothing   -> LetT (Named "letx" (go level scope e2)) (AppT (go (inc level) scope e1) (VarA (Named "letx" (IdxV 0)))) }
    ; LamE  name body -> LamT (Named name (go (inc level) (trieInsert name (LevL level) scope) body))
    ; LetE  defs body -> case defs of { Nil -> go level scope body ; Cons defin rest -> case located defin of 
        { Defin name rhs -> let { tm = go level scope rhs ; scope' = trieInsert name (LevL level) scope }
                            in  LetT (Named name tm) (go (inc level) scope' (LetE rest body)) } }
    ; RecE  defs body -> let { n = length defs ; level' = plus level n
        ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
        ; scope' = foldl f scope (zip (map ldefinedName defs) (rangeFrom level n))
        } in RecT n (map (goDefin level' scope') defs) (go level' scope' body)
    ; CaseE lwhat brs -> case lwhat of { Located loc what -> case mbAtom level scope what of
        { Just atom -> goCase level scope loc atom brs
        ; Nothing   -> LetT (Named "scrut" (go level scope what)) (goCase (inc level) scope loc (VarA (Named "scrut" (IdxV 0))) brs) }}
    ; LitE  lit -> case lit of
        { StrL cs -> go level scope (ListE (map (\x -> LitE (ChrL x)) cs))
        ; _       -> AtmT (KstA lit) }
    ; ListE exprs -> case exprs of 
        { Nil       -> AtmT (ConA (Named "Nil" con_Nil))
        ; Cons e es -> go level scope (AppE (AppE (VarE (fakeLocated "Cons")) e) (ListE es)) }
    ; PrimE prim args -> case prim of { PrimOp _arity pri -> case isLazyPrim pri of 
        { False -> goPrim prim 0 level scope Nil args 
      --  { False -> goArgs level scope args (PriT prim 
      --      (zipWithIndex (\i j -> VarA (Named (appendInt "name" j) (IdxV i))) (reverse (range (length args))) ))
        ; True  -> LZPT prim (map (go level scope) args) }}
    }
  -- ; finishPrim :: PrimOp -> List (Either Term Atom) -> Int -> Term 
  ; finishPrim prim theEis ofs = let 
      { theVars = zipWithIndex (\i j -> VarA (Named (appendInt "parg" j) (IdxV i))) (reverse (range ofs)) 
      ; nameIt var x = case var of { VarA named -> case named of { Named n _ -> Named n x }} 
      ; worker eis vars atoms = case eis of { Nil -> PriT prim (reverse atoms) ; Cons ei eis' -> case ei of
          { Right atom -> worker eis' vars (Cons (shiftAtomRight ofs atom) atoms) 
          ; Left  term -> case vars of { Cons var vars' -> LetT (nameIt var term) (worker eis' vars' (Cons var atoms)) }}}
      } in worker theEis theVars Nil
  -- ; goPrim :: PrimOp -> Int -> Level -> Scope -> List (Either Term Atom) -> List Expr -> Term 
  ; goPrim prim ofs level scope newargs oldargs = case oldargs of 
      { Nil            -> finishPrim prim (reverse newargs) ofs 
      ; Cons this rest -> case mbAtom (minus level ofs) scope this of 
        { Just atom -> goPrim prim      ofs       level  scope (Cons (Right atom                 ) newargs) rest 
        ; Nothing   -> goPrim prim (inc ofs) (inc level) scope (Cons (Left  (go level scope this)) newargs) rest }}
  -- ; goArgs level scope args body = case args of 
  --     { Nil            -> body 
  --     ; Cons this rest -> LetT (go level scope this) (goArgs (inc level) scope rest body) }
  ; goDefin level scope defin = case located defin of { Defin name what -> Named name (go level scope what) }
  ; goCase level scope loc var branches = CasT (Located loc var) (map goBranch branches) where
    { goBranch branch = case branch of
        { DefaultE         rhs -> DefaultT (go level scope rhs)
        ; BranchE con args rhs -> let { n = length args ; level' = plus level n
          ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
          ; scope' = foldl f scope (zip args (rangeFrom level n))
          } in BranchT (Named con (lookupCon dcontable con)) n (go level' scope' rhs) } } }

--------------------------------------------------------------------------------
