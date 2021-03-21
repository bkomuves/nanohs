
{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module PrimOps where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}

--------------------------------------------------------------------------------
-- ** Primops

data Prim
  = Negate | Plus | Minus | Times | Div | Mod | Chr | Ord 
  | BitAnd | BitOr | BitXor | ShiftL | ShiftR
  | IFTE | Not | And | Or | GenEQ | IntEQ | IntLT | IntLE
  | GetChar | PutChar | GetArg | Exit | Error | Print | RunIO | IOBind | IOReturn 
  | OpenFile | HClose | HGetChar | HPutChar | HPutStr | StdIn | StdOut | StdErr
  deriving (Eq,Show)

isLazyPrim :: Prim -> Bool
isLazyPrim prim = case prim of
  { IFTE -> True
  ; And  -> True
  ; Or   -> True 
  ; _    -> False }

showPrim :: Prim -> String
showPrim prim = case prim of
  { Negate   -> "Negate"   ; Plus     -> "Plus"     ; Minus   -> "Minus"
  ; Times    -> "Times"    ; Div      -> "Div"      ; Mod     -> "Mod"
  ; BitAnd   -> "BitAnd"   ; BitOr    -> "BitOr"    ; BitXor  -> "BitXor"
  ; ShiftL   -> "ShiftL"   ; ShiftR   -> "ShiftR"    
  ; Chr      -> "Chr"      ; Ord      -> "Ord"      ; IFTE    -> "IFTE"
  ; Not      -> "Not"      ; And      -> "And"      ; Or      -> "Or"
  ; IntEQ    -> "IntEQ"    ; IntLT    -> "IntLT"    ; IntLE   -> "IntLE"
  ; GenEQ    -> "GenEQ"    ; Error    -> "Error"    ; Exit    -> "Exit" 
  ; GetChar  -> "GetChar"  ; PutChar  -> "PutChar"  ; GetArg  -> "GetArg" 
  ; StdIn    -> "StdIn"    ; StdOut   -> "StdOut"   ; StdErr  -> "StdErr" 
  ; HGetChar -> "HGetChar" ; HPutChar -> "HPutChar" ; HClose  -> "HClose" 
  ; OpenFile -> "OpenFile" ; HPutStr  -> "HPutStr"  ; Print   -> "Print" 
  ; IOBind   -> "IOBind"   ; IOReturn -> "IOReturn" ; RunIO   -> "RunIO"    }

data PrimOp = PrimOp Arity Prim deriving Show

primops :: Trie PrimOp
primops = trieFromList
  [ Pair "error"     (PrimOp  1       Error   )
  , Pair "negate"    (PrimOp  1       Negate  )
  , Pair "plus"      (PrimOp  2       Plus    )
  , Pair "minus"     (PrimOp  2       Minus   )
  , Pair "times"     (PrimOp  2       Times   )
  , Pair "div"       (PrimOp  2       Div     )
  , Pair "mod"       (PrimOp  2       Mod     )
  , Pair "bitAnd"    (PrimOp  2       BitAnd  ) 
  , Pair "bitOr"     (PrimOp  2       BitOr   )
  , Pair "bitXor"    (PrimOp  2       BitXor  ) 
  , Pair "shiftL"    (PrimOp  2       ShiftL  )
  , Pair "shiftR"    (PrimOp  2       ShiftR  )
  , Pair "chr"       (PrimOp  1       Chr     )
  , Pair "ord"       (PrimOp  1       Ord     )
  , Pair "ifte"      (PrimOp  3       IFTE    )
  , Pair "not"       (PrimOp  1       Not     )
  , Pair "and"       (PrimOp  2       And     )
  , Pair "or"        (PrimOp  2       Or      )
  , Pair "geq"       (PrimOp  2       GenEQ   )
  , Pair "eq"        (PrimOp  2       IntEQ   )
  , Pair "lt"        (PrimOp  2       IntLT   )
  , Pair "le"        (PrimOp  2       IntLE   )
  , Pair "getChar"   (PrimOp (inc 0)  GetChar )
  , Pair "putChar"   (PrimOp (inc 1)  PutChar )
  , Pair "getArg"    (PrimOp (inc 1)  GetArg  )
  , Pair "exit"      (PrimOp (inc 1)  Exit    )
  , Pair "openFile"  (PrimOp (inc 2)  OpenFile)
  , Pair "hClose"    (PrimOp (inc 1)  HClose  )
  , Pair "hGetChar"  (PrimOp (inc 1)  HGetChar)
  , Pair "hPutChar"  (PrimOp (inc 2)  HPutChar)
  , Pair "hPutStr"   (PrimOp (inc 2)  HPutStr )
  , Pair "print"     (PrimOp (inc 1)  Print   )
  , Pair "iobind"    (PrimOp (inc 2)  IOBind  )
  , Pair "ioreturn"  (PrimOp (inc 1)  IOReturn)
  , Pair "stdin"     (PrimOp  0       StdIn   )
  , Pair "stdout"    (PrimOp  0       StdOut  )
  , Pair "stderr"    (PrimOp  0       StdErr  )
  , Pair "runIO"     (PrimOp  1       RunIO   )
  ]

--------------------------------------------------------------------------------
