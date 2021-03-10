
-- | The evaluator (interpreter)

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists#-}

module Eval where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import PrimOps
import DataCon
import Core

{-% include "Base.hs"       %-}
{-% include "Types.hs"      %-}
{-% include "Containers.hs" %-}
{-% include "PrimOps.hs"    %-}
{-% include "DataCon.hs"    %-}
{-% include "Core.hs"       %-}

--------------------------------------------------------------------------------
-- ** Runtime values

-- | Note: for recursive lets, we need some delaying mechanism; currently
-- this is done using the @ThkV@ (Thunk) constructor (which was added only
-- for this purpose).
data Value
  = IntV Int
  | ChrV Char
  | ConV Con (List Value)
  | LamV (Value -> Value)
  | ThkV Env Term

-- -- | Force thunks
-- forceValue :: Value -> Value
-- forceValue val = case val of { ThkV env tm -> eval env tm ; _ -> val }

-- showValue :: Value -> String
-- showValue value = case value of
--   { IntV n -> showInt n
--   ; ChrV c -> quoteChar c
--   ; ConV con args -> let { tag = appendInt "Con#" con } in case args of { Nil -> tag
--     ; Cons _ _ -> parenString (unwords (Cons tag (map showValue args))) }
--   ; LamV   _ -> "<lambda>"
--   ; ThkV env tm -> showValue (eval env tm)
--   }
-- 
-- eqValue :: Value -> Value -> Bool
-- eqValue val1 val2 = case val1 of
--   { IntV i1 -> case val2 of { IntV i2 ->  eq i1 i2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
--   ; ChrV c1 -> case val2 of { ChrV c2 -> ceq c1 c2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
--   ; ConV con1 args1 -> case val2 of
--       { ConV con2 args2 -> and3 (eq con1 con2) (eq (length args1) (length args2))
--                                 (andList (zipWith eqValue args1 args2))
--       ; ThkV env2 tm2   -> eqValue val1 (eval env2 tm2)
--       ; _ -> False }
--   ; LamV _        -> False
--   ; ThkV env1 tm1 -> eqValue (eval env1 tm1) val2
--   }

boolToValue :: Bool -> Value
boolToValue b = ifte b (ConV con_True Nil) (ConV con_False Nil)

valueToBool :: Value -> Bool
valueToBool val = case val of { ConV con args -> eq con con_True ; _ -> error "not a boolean" }

intToValue :: Int -> Value
intToValue = IntV

valueToInt :: Value -> Int
valueToInt val = case val of { IntV x -> x ; _ -> error "not an integer" }

charToValue :: Char -> Value
charToValue = ChrV

maybeCharToValue :: Maybe Char -> Value
maybeCharToValue mb = case mb of { Nothing -> ConV con_Nothing Nil ; Just c -> ConV con_Just (singleton (ChrV c)) }

valueToChar :: Value -> Char
valueToChar val = case val of { ChrV c -> c ; _ -> error "not a character" }

unitToValue :: Unit -> Value
unitToValue Unit = ConV con_Unit Nil

valueToUnit :: Value -> Unit
valueToUnit val = case val of { ConV con _ -> ifte (eq con con_Unit) Unit err ; _ -> err } where
  { err = error "not a unit" }

listToValue :: List Value -> Value
listToValue list = case list of { Nil -> ConV con_Nil Nil
  ; Cons x xs -> ConV con_Cons [ x , listToValue xs ] }

valueToList :: Value -> List Value
valueToList value = case value of
  { ConV con args -> ifte (neq con con_Cons) Nil
      (case mbPair args of { Nothing -> Nil ; Just pair -> case pair of
        { Pair u v -> Cons u (valueToList v) } } ) }

stringToValue :: String -> Value
stringToValue = compose listToValue (map charToValue)

valueToString :: Value -> String
valueToString = compose (map valueToChar) valueToList

maybeStringToValue :: Maybe String -> Value
maybeStringToValue mb = case mb of { Nothing -> ConV con_Nothing Nil ; Just s -> ConV con_Just (singleton (stringToValue s)) }

--------------------------------------------------------------------------------
-- ** Evaluating primops

evalfunII :: (Int -> Int) -> Value -> Value
evalfunII f v1 = intToValue (f (valueToInt v1))

evalfunIII :: (Int -> Int -> Int) -> Value -> Value -> Value
evalfunIII f v1 v2 = intToValue (f (valueToInt v1) (valueToInt v2))

evalfunIIB :: (Int -> Int -> Bool) -> Value -> Value -> Value
evalfunIIB f v1 v2 = boolToValue (f (valueToInt v1) (valueToInt v2))

evalfunBB :: (Bool -> Bool) -> Value -> Value
evalfunBB f v1 = boolToValue (f (valueToBool v1))

evalfunBBB :: (Bool -> Bool -> Bool) -> Value -> Value -> Value
evalfunBBB f v1 v2 = boolToValue (f (valueToBool v1) (valueToBool v2))

unary   :: List a -> (a -> b)           -> b
binary  :: List a -> (a -> a -> b)      -> b
ternary :: List a -> (a -> a -> a -> b) -> b
unary   args f = case args of { Cons x xs -> f x             ; Nil -> error "unary: not enough arguments"   }
binary  args f = case args of { Cons x xs -> unary  xs (f x) ; Nil -> error "binary: not enough arguments"  }
ternary args f = case args of { Cons x xs -> binary xs (f x) ; Nil -> error "ternary: not enough arguments" }

evalPrim :: Prim -> List Value -> Value
evalPrim prim args = case prim of
  { Error   -> unary   args (compose error valueToString)
  ; Negate  -> unary   args (evalfunII  negate)
  ; Plus    -> binary  args (evalfunIII plus  )
  ; Minus   -> binary  args (evalfunIII minus )
  ; Times   -> binary  args (evalfunIII times )
  ; Div     -> binary  args (evalfunIII div   )
  ; Mod     -> binary  args (evalfunIII mod   )
  ; Chr     -> unary   args (compose3 charToValue chr valueToInt )
  ; Ord     -> unary   args (compose3 intToValue  ord valueToChar)
  ; Not     -> unary   args (evalfunBB  not )
  ; IntEQ   -> binary  args (evalfunIIB eq  )
  ; IntLT   -> binary  args (evalfunIIB lt  )
  ; IntLE   -> binary  args (evalfunIIB le  )
  ; GetChar -> unary   args (compose3 maybeCharToValue   (\u -> getChar# u) valueToUnit)
  ; PutChar -> unary   args (compose3 unitToValue        (\c -> putChar# c) valueToChar)
  ; Exit    -> unary   args (compose3 unitToValue        (\k -> exit#    k) valueToInt )
  ; GetArg  -> unary   args (compose3 maybeStringToValue (\n -> getArg#  n) valueToInt ) 
  ; _       -> error "evalPrim: unimplemented primop"
  }
--  ; GenEQ   -> binary  args (\x y -> boolToValue (eqValue x y))
--  ; IFTE    -> error "ifte: this has to be implemented somewhere else because of lazyness"
--  ; And     -> binary  args (evalfunBBB and )
--  ; Or      -> binary  args (evalfunBBB or  )

--------------------------------------------------------------------------------
-- ** The evaluator

-- in reverse order as usual
type Env = List Value

-- evalVar :: Env -> Idx -> Value
-- evalVar env idx = forceValue (index idx env)
-- 
-- eval :: Env -> Term -> Value
-- eval env term = case term of
--   { VarT idx     -> evalVar env (forgetName idx)
--   ; ConT con     -> ConV (forgetName con) Nil
--   ; AppT e1 a2   -> case eval env e1 of
--     { LamV fun      -> fun                 (evalVar env (forgetName a2))
--     ; ConV con args -> ConV con (snoc args (evalVar env (forgetName a2)))
--     ; _             -> error "application to non-lambda (int/char)" }
--   ; PriT primop vs -> case primop of { PrimOp _arity prim -> evalPrim prim (map (evalVar env) vs) }
--   ; LZPT primop ts -> case primop of { PrimOp _arity prim -> case prim of
--     { IFTE -> ternary ts (lazyIFTE env)
--     ; And  -> binary  ts (lazyAnd  env)
--     ; Or   -> binary  ts (lazyOr   env)
--     ; _    -> error "unrecognized lazy primop" }}
--   ; LamT body    -> LamV (\x -> eval (Cons x env) (forgetName body))
--   ; CasT var brs -> case forceValue (index var env) of
--     { ConV con args -> matchCon env con args brs
--     ; _             -> error "branching on a non-constructor (lambda)" }
--   ; RecT n ls tm -> let { env' = append (reverse (map (mkThunk env') ls)) env } in eval env' tm
--   ; KstT lit     -> case lit of
--     { IntL k       -> IntV k
--     ; ChrL c       -> ChrV c
--     ; StrL _       -> error "string literals should not appear in core" }
--   } 
--   where { mkThunk env1 named = case named of { Named name body -> ThkV env1 body } }
-- 
-- lazyIFTE :: Env -> Term -> Term -> Term -> Value
-- lazyIFTE env tb tx ty = let { vb = eval env tb } in ifte (valueToBool vb) (eval env tx) (eval env ty)
-- 
-- lazyAnd :: Env -> Term -> Term -> Value
-- lazyAnd env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (eval env t2) (boolToValue False)
-- 
-- lazyOr :: Env -> Term -> Term -> Value
-- lazyOr env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (boolToValue True) (eval env t2)
-- 
-- matchCon :: Env -> Con -> List Value -> List BranchT -> Value
-- matchCon env con args = go where
--   { nargs = length args
--   ; go branches = case branches of
--     { Nil -> error "non-exhaustive patterns in case"
--     ; Cons this rest -> case this of
--       { DefaultT rhs            -> eval env rhs
--       ; BranchT bcon bnargs rhs -> ifte (and (eq con (forgetName bcon)) (eq nargs bnargs))
--           (eval (append (reverse args) env) rhs)
--           (go rest) } } }

--------------------------------------------------------------------------------
