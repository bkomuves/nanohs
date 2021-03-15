
-- | Data constructors

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module DataCon where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import Syntax

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "Syntax.hs"     %-}

--------------------------------------------------------------------------------
-- ** Data constructors

isDCon :: Name -> Bool
isDCon name = isUpper (head name)

-- -- | Mapping constructor names to constructor tags
-- type DataConTable = Trie Con

con_False   = 0
con_True    = 1
con_Unit    = 2
con_Nil     = 3
con_Cons    = 4
con_Nothing = 5
con_Just    = 6
con_Pair          = 7
con_RealWorld     = 8
con_ReadMode      = 9
con_WriteMode     = 10
con_AppendMode    = 11
con_ReadWriteMode = 12

type DConState = Pair Int DataConTable

initialDConState :: DConState
initialDConState = Pair 13 (trieFromList predefinedDataCons)

predefinedDataCons :: List (Pair String Int)
predefinedDataCons =
  [ Pair "False" con_False , Pair "True" con_True , Pair "Unit"    con_Unit    , Pair "Pair" con_Pair
  , Pair "Nil"   con_Nil   , Pair "Cons" con_Cons , Pair "Nothing" con_Nothing , Pair "Just" con_Just 
  , Pair "ReadMode"   con_ReadMode   , Pair "WriteMode"     con_WriteMode      , Pair "RealWorld" con_RealWorld   
  , Pair "AppendMode" con_AppendMode , Pair "ReadWriteMode" con_ReadWriteMode ]

-- | Collect data constructors from the source.
--
-- Encoding of constructors tags:
--
-- *  0 = False
-- *  1 = True
-- *  2 = Unit
-- *  3 = Nil
-- *  4 = Cons
-- *  5 = Nothing
-- *  6 = Just
-- *  7 = Pair
-- *  8 = RealWorld
-- *  9 = ReadMode
-- * 10 = WriteMode
-- * 11 = AppendMode
-- * 12 = ReadWriteMode
-- * 11 = IO
-- * 12.. = user defined constructors
--
-- We need to fix Int, Char, False, True, Unit, Nil, Cons, Just and Nothing
-- and the file modes because the primops use them
--
collectDataCons :: Program Expr -> DataConTable
collectDataCons defins = snd (execState action initialDConState) where
  { action = smapM_ collectDataConsWorker (map definedWhat defins) }

collectDataConsWorker :: Expr -> State DConState Unit
collectDataConsWorker expr = go expr where
  { insert name = sbind sget (\pair -> case pair of { Pair n table -> case trieLookup name table of
    { Just k  -> sreturn Unit
    ; Nothing -> sput (Pair (inc n) (trieInsert name n table)) } })
  ; go expr = case expr of
    { VarE lnam   -> let { name = located lnam } in case isDCon name of { False -> sreturn Unit ; True -> insert name }
    ; StrE k      -> sreturn Unit
    ; AppE e1 e2  -> sseq (go e1) (go e2)
    ; LamE _ body -> go body
    ; LetE defs body -> goLet defs body
    ; RecE defs body -> goLet defs body
    ; CaseE e branches -> sseq (go e) (smapM_ (\br -> case br of
        { BranchE con _ rhs -> sbind (insert con) (\_ -> go rhs)
        ; DefaultE      rhs -> go rhs }) branches)
    ; LitE _     -> sreturn Unit
    ; ListE list -> smapM_ go list
    ; PrimE _ as -> smapM_ go as
    } 
  ; goLet defs body = sseq 
      (smapM_ (\defin -> case defin of { Defin _ rhs -> go rhs }) defs ) (go body) }

--------------------------------------------------------------------------------
