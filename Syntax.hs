
-- | Surface syntax

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Syntax where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
-- import Core
import PrimOps

{-% include "Base.hs"        %-}
{-% include "Containers.hs"  %-}
{-% include "Types.hs"       %-}
-- {-% include "Core.hs"        %-}
{-% include "PrimOps.hs"     %-}

--------------------------------------------------------------------------------
-- * Surface syntax

type DefinE = Defin Expr

-- | We \"parse\" (well, recognize) type declarations, data declarations,
-- type synonyms and imports, but we ignore them; this is simply so that the
-- this source code can be a valid Haskell program and self-hosting at the
-- same time.
data TopLevel
  = TopDefin    DefinE
  | TopTyDecl   Name (List Token)
  | TopDataDecl (List Token)
  | TopTyAlias  (List Token)
  | TopImport   (List Token)
  | TopInclude  FilePath
  | TopModule   (List Token)
  deriving Show

filterIncludes :: List TopLevel -> List FilePath
filterIncludes = go where { go ls = case ls of { Nil -> Nil ; Cons this rest ->
  case this of { TopInclude fn -> Cons fn (go rest) ; _ -> go rest }}}

mbDefin :: TopLevel -> Maybe DefinE
mbDefin toplev = case toplev of { TopDefin def -> Just def ; _ -> Nothing }

--------------------------------------------------------------------------------

data Expr
  = VarE  LName
  | AppE  Expr Expr
  | LamE  Name Expr
  | LetE  (List DefinE) Expr
  | RecE  (List DefinE) Expr
  | CaseE Expr (List BranchE)
  | LitE  Literal
  | ListE (List Expr)
  | PrimE PrimOp (List Expr)
  | StrE  Int
  deriving Show

data BranchE
  = BranchE Name (List Name) Expr
  | DefaultE Expr
  deriving Show

-- data BranchE
--   = BranchE Pattern Expr
--   deriving Show

isLambdaExpr :: Expr -> Bool
isLambdaExpr expr = case expr of { LamE _ _ -> True ; _ -> False }

lamsE :: List Name -> Expr -> Expr
lamsE args body = case args of { Nil -> body ; Cons v vs -> LamE v (lamsE vs body) }

appsE :: Expr -> List Expr -> Expr
appsE fun  args = case args of { Nil -> fun  ; Cons t ts -> appsE (AppE fun t) ts  }

listAppsE :: List Expr -> Expr
listAppsE  list = case list of { Cons f args -> appsE f args ; Nil -> error "listAppsE" }

--------------------------------------------------------------------------------
-- ** TODO: Pattern compiler 

-- SimP  = simple pattern (we compile down to this)
-- AppP  = constructor pattern
-- VarP  = variable pattern
-- WildP = wildcard patterns
-- ListP = list pattern
data Pattern
  = SimP Name (List Name)      
  | AppP Name (List Pattern)   
  | VarP Name                  
  | WildP                      
  | ListP (List Pattern)       
  deriving Show

patternHead :: Pattern -> Maybe Name
patternHead pat = case pat of
  { SimP con _list -> Just con
  ; AppP con _list -> Just con
  ; _              -> Nothing }

-- -- | We translate complex pattern into iterated matching of simple patterns
-- patternCompiler :: List BranchE -> List BranchE
-- patternCompiler

--------------------------------------------------------------------------------
-- ** free and bound variables

-- | Free variables in an expression
freeVars :: Expr -> TrieSet
freeVars expr = go trieEmpty expr where
  { go bound expr = case expr of
    { VarE lname     -> let { nam = located lname } in case trieMember nam bound of { False -> trieSetSingleton nam ; _ -> trieEmpty }
    ; AppE e1 e2     -> trieUnion (go bound e1) (go bound e2)
    ; LamE v body    -> go (trieSetInsert v bound) body
    ; LetE defs body -> goLets   bound defs body
    ; RecE defs body -> goLetRec bound defs body
    ; CaseE what brs -> trieUnion (go bound what) (trieUnions (map (goBranch bound) brs))
    ; LitE  _        -> trieEmpty
    ; ListE list     -> trieUnions (map (go bound) list)
    ; PrimE p list   -> trieUnions (map (go bound) list)
    ; StrE  _        -> trieEmpty }
  ; goBranch bound branch = case branch of
    { DefaultE rhs     -> go bound rhs 
    ; BranchE _ ns rhs -> let { bound' = trieUnion (trieSetFromList ns) bound } in go bound' rhs }
  ; goLets bound defs body = case defs of { Nil -> go bound body ; Cons def rest -> case def of { Defin nam rhs ->
      let { bound' = trieSetInsert nam bound } in trieUnion (go bound rhs) (goLets bound' rest body) } }
  ; goLetRec bound defs body = let 
      { bound' = trieUnion (trieSetFromList (map definedName defs)) bound 
      ; stuff = map (\defin -> go bound' (definedWhat defin)) defs
      } in trieUnion (trieUnions stuff) (go bound' body) }

--------------------------------------------------------------------------------
-- ** recognize PrimOps

-- | From @((f x) y) z@ we create the list [f,x,y,z]
recogAppsE :: Expr -> List Expr
recogAppsE = compose reverse go where
  { go expr = case expr of { AppE f x -> Cons x (go f)  ; _ -> singleton expr } }

-- | temporary argument names for saturating primops. Note that all primops have at most 3 arguments
tmpVars :: List Name
tmpVars = ["x1","x2","x3","x4","x5"]
-- tmpVars = map (\i -> append "x" (showInt i)) (rangeFrom 1 5)

-- | Saturate primop application
saturatePrimApp :: Location -> PrimOp -> List Expr -> Expr
saturatePrimApp loc primop args = case primop of { PrimOp arity prim -> case compare nargs arity of
  { EQ ->        PrimE primop args
  ; GT -> appsE (PrimE primop (take arity args)) (drop arity args)
  ; LT -> let { vars = take (minus arity nargs) tmpVars }
          in  lamsE vars (PrimE primop (append args (map (\v -> VarE (Located loc v)) vars)))
  } }
  where { nargs = length args }

-- | Recognize primop applications, and saturate them if necessary
recogPrimApps :: Program Expr -> Program Expr
recogPrimApps prg = map (fmapDefin recogPrimApps1) prg

-- | Recognize primop applications, and saturate them if necessary
recogPrimApps1 :: Expr -> Expr
recogPrimApps1 = go where
  { goVar lname = case trieLookup (located lname) primops of
      { Nothing        -> VarE lname
      ; Just primop    -> saturatePrimApp (location lname) primop [] }
  ; go expr = case expr of
      { VarE lname      -> goVar lname
      ; AppE _ _       -> case recogAppsE expr of { Cons f args -> case f of
          { VarE ln      -> case trieLookup (located ln) primops of
              { Nothing     -> appsE (VarE ln)                      (map go args)
              ; Just primop -> saturatePrimApp (location ln) primop (map go args) }
          ; _            -> appsE (go    f) (map go args) } }
      ; LamE arg  body -> LamE  arg  (go body)
      ; LetE defs body -> LetE  (map goDefin defs) (go body)
      ; RecE defs body -> RecE  (map goDefin defs) (go body)
      ; CaseE what brs -> CaseE (go what) (map goBranch brs)
      ; ListE exprs    -> ListE (map go exprs)
      ; _              -> expr }
  ; goBranch branch = case branch of
      { BranchE con args rhs -> BranchE con args (go rhs)
      ; DefaultE         rhs -> DefaultE         (go rhs) }
  ; goDefin defin = case defin of
      { Defin name expr -> Defin name (go expr) } }

--------------------------------------------------------------------------------
-- * extract string constants

type StrState  = Pair Int (List String)
type Stringy a = State StrState a

addString :: String -> Stringy Int
addString what = sbind sget (\pair -> case pair of { Pair n list -> 
                 sbind (sput (Pair (inc n) (Cons what list))) (\_ -> sreturn n) })

extractStringConstants :: Program Expr -> Pair (List String) (Program Expr)
extractStringConstants program = case runState (smapM worker program) (Pair 0 Nil) of
  { Pair fstate prg' -> Pair (reverse (snd fstate)) prg' } 
  where { worker defin = case defin of { Defin name rhs -> sfmap (Defin name) (extractStringConstants1 rhs) } }

extractStringConstants1 :: Expr -> Stringy Expr 
extractStringConstants1 expr = go expr where
  { go expr = case expr of
    { LitE  lit      -> case lit of { StrL str  -> sfmap StrE (addString str) ; _ -> sreturn expr }
    ; VarE  _        -> sreturn expr
    ; AppE  e1 e2    -> sliftA2 AppE (go e1) (go e2)
    ; LamE  n body   -> sfmap  (LamE n) (go body)
    ; LetE  defs rhs -> sliftA2 LetE  (smapM goDefin defs) (go rhs)
    ; RecE  defs rhs -> sliftA2 RecE  (smapM goDefin defs) (go rhs)
    ; CaseE what brs -> sliftA2 CaseE (go what) (smapM goBranch brs)
    ; ListE ls       -> sfmap   ListE (smapM go ls)
    ; PrimE pri args -> sfmap  (PrimE pri) (smapM go args) }
  ; goDefin  defin  = case defin of { Defin name rhs -> sfmap (Defin name) (go rhs) }
  ; goBranch branch = case branch of 
    { BranchE con args rhs -> sfmap (BranchE con args) (go rhs)
    ; DefaultE         rhs -> sfmap (DefaultE        ) (go rhs) } }

--------------------------------------------------------------------------------


