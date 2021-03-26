
-- | The evaluator (interpreter). 
--
-- Note: this is not needed for compilation, it's simply provided as an extra.
--

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

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

-- | Note: for recursive lets, we need some delaying mechanism, because
-- this is a strict language, so we don't have cyclic data structures.
--
-- The idea is that in case of a letrec, the first two argument of LamV
-- store the recursive part, and the third stores the rest of the environment.
data Value
  = IntV Int
  | ChrV Char
  | HdlV Handle
  | ConV Con (List Value)
  | LamV (Value -> EvalM Value)
  | IO_V Action

-- | This is a \"newtype\" only because the two layers of IO was really confusing...
data Action = Action (IO Value)

runAction :: Action -> IO Value
runAction action = case action of { Action m -> m }

showValue_ :: Value -> String
showValue_ value = showValue Nil value

showValue' :: StaticEnv -> Value -> String
showValue' statenv val = case statenv of { StaticEnv dconNames _ _ -> showValue dconNames val }

type DConNames = Map Int String

showValue :: DConNames -> Value -> String
showValue conNames value = case value of
  { IntV n -> showInt n
  ; ChrV c -> quoteChar c
  ; HdlV _ -> "<file handle>"
  ; ConV con args ->
      let { tag = case mapLookup con conNames of { Just name -> name ; Nothing -> appendInt "Con#" con } }
      in  case args of { Nil -> tag ; Cons _ _ -> parenString (unwords (Cons tag (map (showValue conNames) args))) }
  ; LamV _ -> "<lambda>"
  ; IO_V _ -> "<IO action>"
  }

printValue :: DConNames -> Value -> IO Unit
printValue conNames x = putStrLn (showValue conNames x)

eqValue :: Value -> Value -> Bool
eqValue val1 val2 = case val1 of
  { IntV i1 -> case val2 of { IntV i2 ->  eq i1 i2 ; _ -> False }
  ; ChrV c1 -> case val2 of { ChrV c2 -> ceq c1 c2 ; _ -> False }
  -- ; HdlV h1 -> case val2 of { HdlV h2 -> heq h1 h2 ; _ -> False }
  ; ConV con1 args1 -> case val2 of
      { ConV con2 args2 -> and3 (eq con1 con2) (eq (length args1) (length args2))
                                (andList (zipWith eqValue args1 args2))
      ; _ -> False }
  ; LamV _   -> False
  ; IO_V _   -> False
  }

--------------------------------------------------------------------------------
-- ** Marshalling values

boolToValue :: Bool -> Value
boolToValue b = ifte b (ConV con_True Nil) (ConV con_False Nil)

valueToBool :: Value -> Bool
valueToBool val = case val of { ConV con args -> eq con con_True ; _ -> error "marshalling: not a boolean" }

intToValue :: Int -> Value
intToValue = IntV

valueToInt :: Value -> Int
valueToInt val = case val of { IntV x -> x ; _ -> error "marshalling: not an integer" }

charToValue :: Char -> Value
charToValue = ChrV

maybeCharToValue :: Maybe Char -> Value
maybeCharToValue mb = case mb of { Nothing -> ConV con_Nothing Nil ; Just c -> ConV con_Just (singleton (ChrV c)) }

valueToChar :: Value -> Char
valueToChar val = case val of { ChrV c -> c ; _ -> error "marshalling: not a character" }

unitToValue :: Unit -> Value
unitToValue Unit = ConV con_Unit Nil

valueToUnit :: Value -> Unit
valueToUnit val = case val of { ConV con _ -> ifte (eq con con_Unit) Unit err ; _ -> err } where
  { err = error "marshalling: not a unit" }

handleToValue :: Handle -> Value
handleToValue = HdlV

valueToHandle :: Value -> Handle
valueToHandle val = case val of { HdlV h -> h ; _ -> error "marshalling: not a handle" }

valueToIOMode :: Value -> IOMode
valueToIOMode value = case value of
  { ConV con args -> ifte (eq con con_ReadMode      ) ReadMode      ( 
                     ifte (eq con con_WriteMode     ) WriteMode     ( 
                     ifte (eq con con_AppendMode    ) AppendMode    ( 
                     ifte (eq con con_ReadWriteMode ) ReadWriteMode (err value))))
  ; _ -> err value } where { err v = error (append "marshalling: not an IO mode: " (quoteString (showValue_ v))) }
                          
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

literalToValue :: Literal -> Value
literalToValue lit = case lit of
  { IntL k       -> IntV k
  ; ChrL c       -> ChrV c
  ; StrL s       -> stringToValue s }

--------------------------------------------------------------------------------
-- ** The environment

-- | The environment. We need some hacking to handle letrec blocks - as we cannot have cyclic data structure, we have to
-- do something else. So we just simulate the stack allocation structure.
data Env 
  = NilEnv
  | ConsEnv Value Env
  | RecEnv  Int (List Term) Env

indexEnv :: StaticEnv -> Int -> Env -> Value
indexEnv statEnv k env = go k env where 
  { go k env = case env of
    { NilEnv             -> error "indexEnv: indexing out of bounds"
    ; ConsEnv val   rest -> ifte (eq k 0)  val                                       (go (dec   k  ) rest)
    ; RecEnv  n tms rest -> ifte (lt k n) (mkLamV statEnv env (unLam (index k tms))) (go (minus k n) rest) }
  ; unLam tm = case tm of { LamT nt -> forgetName nt ; _ -> error "indexEnv: fatal: recursive binding must be lambda" } }

lengthEnv :: Env -> Int
lengthEnv env = case env of { NilEnv -> 0 ; ConsEnv _ rest -> inc (lengthEnv rest) ; RecEnv n _ rest -> plus n (lengthEnv rest) }

-- -- | for debugging only
-- showEnv :: Env -> String
-- showEnv env = Cons '[' (go env) where { go env = case env of
--   { NilEnv            -> "]" 
--   ; ConsEnv v rest    -> append3 (showValue_ v)     " : " (go rest)  
--   ; RecEnv _ tms rest -> append3 (showTermList tms) " : " (go rest) }}
-- 
-- -- | for debugging only
-- printEnv :: Env -> IO Unit
-- printEnv env = go 0 env where { go k env = case env of
--   { NilEnv            -> ioret_ 
--   ; ConsEnv v rest    -> ioseq (putStrLn (append3 (showInt k) " => " (showValue_     v))) (go (inc  k)   rest)
--   ; RecEnv n tms rest -> ioseq (putStrLn (append3 (showInt k) " => " (showTermList tms))) (go (plus k n) rest) }}

--------------------------------------------------------------------------------
-- ** The evaluator

-- | The static execution environment: data constructors, string constants, index of @main@
data StaticEnv = StaticEnv 
  { _dcons   :: Map Int String
  , _strLits :: List String
  , _mainIdx :: TopIdx 
  } 
  deriving Show

pushEnv1 :: Value -> Env -> Env
pushEnv1 value env = ConsEnv value env

pushEnvMany :: List Value -> Env -> Env
pushEnvMany values env = case values of { Nil -> env ; Cons v vs -> pushEnvMany vs (pushEnv1 v env) }

pushEnvRec :: Int -> List Term -> Env -> Env
pushEnvRec n tms env = RecEnv n tms env

evalVar :: StaticEnv -> Env -> Var -> Value
evalVar statEnv env var = case var of
  { IdxV idx -> indexEnv statEnv idx env
  ; StrV k   -> case statEnv of { StaticEnv _dcons strlits _main -> stringToValue (index k strlits) }
  ; TopV _   -> error "evalVar: top-level references shouldn't appear in terms"
  ; LevV _   -> error "evalVar: de Bruijn levels shouldn't appear in terms" }

evalAtom :: StaticEnv -> Env -> Atom -> Value
evalAtom statEnv env atom = case atom of 
  { VarA var -> evalVar statEnv env (forgetName var)
  ; KstA lit -> literalToValue lit
  ; ConA con -> ConV (forgetName con) Nil }

mkLamV :: StaticEnv -> Env -> Term -> Value
mkLamV statEnv env tm = LamV (\x -> eval statEnv (pushEnv1 x env) tm)

-- eval :: StaticEnv -> Env -> Term -> IO Value
-- eval statEnv env term = 
--   ioseq (iosequence_
--   [ putStrLn (append ">> env  = " (showEnv env))
--   , putStrLn (append ">> term = " (showTerm term))
--   , putStrLn "" 
--   ])
--   (eval' statEnv env term)

type EvalM a = IO a

eval :: StaticEnv -> Env -> Term -> EvalM Value
eval statEnv env term = case term of
  { AtmT atom    -> ioreturn (evalAtom statEnv env atom)
  ; AppT e1 a2   -> iobind (eval statEnv env e1) (\val1 -> case val1 of
     { ConV con args  -> ioreturn (ConV con (snoc args (evalAtom statEnv env a2)))
     ; LamV fun       -> let { val2 = evalAtom statEnv env a2 } in fun val2
     ; _              -> error "eval: application to non-lambda" })
  ; PriT primop vs -> case primop of { PrimOp _arity prim -> case statEnv of
      { StaticEnv dconNames _ _ -> evalPrimM dconNames prim (map (evalAtom statEnv env) vs) }}
  ; LZPT primop ts -> case primop of { PrimOp _arity prim -> case prim of
     { IFTE -> ternary ts (lazyIFTE statEnv env)
     ; And  -> binary  ts (lazyAnd  statEnv env)
     ; Or   -> binary  ts (lazyOr   statEnv env)
     ; _    -> error "eval: unrecognized lazy primop" }}
  ; LetT nt1 t2   -> iobind (eval statEnv env (forgetName nt1)) (\x -> eval statEnv (pushEnv1 x env) t2)
  ; LamT body     -> ioreturn (mkLamV statEnv env (forgetName body)) 
  ; CasT latom brs -> let { scrutinee = evalAtom statEnv env (located latom) } in case scrutinee of
     { ConV con args -> matchCon statEnv env con args brs
     ; _             -> error (concat [ "eval: branching on a non-constructor at " , showLocation (location latom), "; scrutinee = " , showValue' statEnv scrutinee ]) }
  ; RecT n nts tm -> let { env' = pushEnvRec n (map forgetName nts) env } in eval statEnv env' tm
  ; MainT         -> case statEnv of { StaticEnv _ _ mainidx -> 
                       let { k = minus (lengthEnv env) (inc mainidx) }
                       in (ioreturn (indexEnv statEnv k env)) }
  } 

matchCon :: StaticEnv -> Env -> Con -> List Value -> List BranchT -> EvalM Value
matchCon statEnv env con args brs = go brs where
  { nargs = length args
  ; go branches = case branches of
    { Nil -> error "non-exhaustive patterns in case"
    ; Cons this rest -> case this of
      { DefaultT rhs            -> eval statEnv env rhs
      ; BranchT bcon bnargs rhs -> ifte (and (eq con (forgetName bcon)) (eq nargs bnargs))
          (eval statEnv (pushEnvMany args env) rhs)
          (go rest) } } }

--------------------------------------------------------------------------------
-- ** Evaluating pure primops

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

evalPrimPure :: Prim -> List Value -> Value
evalPrimPure prim args = case prim of
  { Error   -> unary   args (compose error valueToString)
  ; Negate  -> unary   args (evalfunII  negate)
  ; Plus    -> binary  args (evalfunIII plus  )
  ; Minus   -> binary  args (evalfunIII minus )
  ; Times   -> binary  args (evalfunIII times )
  ; Div     -> binary  args (evalfunIII div   )
  ; Mod     -> binary  args (evalfunIII mod   )
  ; BitAnd  -> binary  args (evalfunIII bitAnd) 
  ; BitOr   -> binary  args (evalfunIII bitOr )
  ; BitXor  -> binary  args (evalfunIII bitXor ) 
  ; ShiftL  -> binary  args (evalfunIII shiftL)
  ; ShiftR  -> binary  args (evalfunIII shiftR)
  ; Chr     -> unary   args (compose3 charToValue chr valueToInt )
  ; Ord     -> unary   args (compose3 intToValue  ord valueToChar)
  ; Not     -> unary   args (evalfunBB  not )
  ; IntEQ   -> binary  args (evalfunIIB eq  )
  ; IntLT   -> binary  args (evalfunIIB lt  )
  ; IntLE   -> binary  args (evalfunIIB le  )
  ; StdIn   -> nullary args (handleToValue stdin )
  ; StdOut  -> nullary args (handleToValue stdout)
  ; StdErr  -> nullary args (handleToValue stderr)
  ; _       -> error (append "evalPrim: unimplemented primop: " (quoteString (showPrim prim)))
  }
--  ; GenEQ   -> binary  args (\x y -> boolToValue (eqValue x y))
--  ; IFTE    -> error "ifte: this has to be implemented somewhere else because of lazyness"
--  ; And     -> binary  args (evalfunBBB and )
--  ; Or      -> binary  args (evalfunBBB or  )

--------------------------------------------------------------------------------
-- ** Evaluating IO primops

ioCompose1 :: (c -> d) -> (b -> IO c) -> (a -> b) -> a -> IO d
ioCompose1 post action pre = \x -> iofmap post (action (pre x))

ioCompose2 :: (c -> d) -> (b1 -> b2 -> IO c) -> (a1 -> b1) -> (a2 -> b2) -> a1 -> a2 -> IO d
ioCompose2 post action pre1 pre2 = \x y -> iofmap post (action (pre1 x) (pre2 y))

-- | Note: since the evaluator is in the IO monad, since it can evaluate
-- side effects, this also results in @(Value -> EvalM Value)@ instead 
-- of @(Value -> Value)@
valueToLambda :: Value -> (Value -> EvalM Value)
valueToLambda val = case val of { LamV fun -> fun ; _ -> error "marshalling: not a lambda" }

actionToValue :: Action -> Value
actionToValue action = IO_V action

valueToAction :: Value -> Action
valueToAction val = case val of { IO_V action -> action ; _ -> error "marshalling: not an IO action" }

actionJoin :: IO Action -> Action
actionJoin io = Action (iojoin (iofmap runAction io))

bindAction :: Action -> (Value -> Action) -> Action
bindAction act1 fun2 = Action (iobind (runAction act1) (compose runAction fun2))

-- | Assuming the values are the right shape for @iobind@, we bind them
ioBindValue :: Value -> Value -> Value
ioBindValue actionVal funVal = actionToValue (bindAction a b) where
  { a = valueToAction actionVal 
  ; b = \val -> actionJoin (iofmap valueToAction (valueToLambda funVal val)) }

-- | Note: This has to be The environment is only used for @IOBind@, which takes a lambda as second argument.
evalPrimM :: DConNames -> Prim -> List Value -> EvalM Value
evalPrimM dconNames prim args = case prim of
  { RunIO    -> runAction (unary  args valueToAction) 
  ; _        -> ioreturn (evalPrimPureIO dconNames prim args) }

evalPrimPureIO :: DConNames -> Prim -> List Value -> Value 
evalPrimPureIO dconNames prim args = case prim of
  { GetChar  -> mkIO (nullary args (iofmap     maybeCharToValue   getChar )                             )
  ; GetArg   -> mkIO (unary   args (ioCompose1 maybeStringToValue getArg   (compose inc2 valueToInt))   )
  ; PutChar  -> mkIO (unary   args (ioCompose1 unitToValue        putChar  valueToChar  )               )
  ; Exit     -> mkIO (unary   args (ioCompose1 unitToValue        exit     valueToInt   )               )
  ; OpenFile -> mkIO (binary  args (ioCompose2 handleToValue      openFile valueToString valueToIOMode) )
  ; HClose   -> mkIO (unary   args (ioCompose1 unitToValue        hClose   valueToHandle)               )    
  ; HGetChar -> mkIO (unary   args (ioCompose1 maybeCharToValue   hGetChar valueToHandle)               )    
  ; HPutChar -> mkIO (binary  args (ioCompose2 unitToValue        hPutChar valueToHandle valueToChar  ) )
  ; HPutStr  -> mkIO (binary  args (ioCompose2 unitToValue        hPutStr  valueToHandle valueToString) )   
  ; Print    -> mkIO (unary   args (ioCompose1 unitToValue        putStrLn (showValue dconNames))       )
  ; IOReturn -> mkIO (unary   args ioreturn)
  ; IOBind   -> binary args ioBindValue                      
  ; _        -> evalPrimPure prim args
  } where { mkIO ioaction = actionToValue (Action ioaction) }

--------------------------------------------------------------------------------
-- *** Lazy primops

lazyIFTE :: StaticEnv -> Env -> Term -> Term -> Term -> IO Value
lazyIFTE statEnv env tb tx ty = iobind (eval statEnv env tb) (\vb -> 
  ifte (valueToBool vb) (eval statEnv env tx) (eval statEnv env ty))

lazyAnd :: StaticEnv -> Env -> Term -> Term -> IO Value
lazyAnd statEnv env t1 t2 = iobind (eval statEnv env t1) (\v1 -> 
  ifte (valueToBool v1) (eval statEnv env t2) (ioreturn (boolToValue False)))

lazyOr :: StaticEnv -> Env -> Term -> Term -> IO Value
lazyOr statEnv env t1 t2 = iobind (eval statEnv env t1) (\v1 -> 
  ifte (valueToBool v1) (ioreturn (boolToValue True)) (eval statEnv env t2))

--------------------------------------------------------------------------------

