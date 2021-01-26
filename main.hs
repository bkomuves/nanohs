
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Main where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show(..) , (++) )
import qualified Prelude

import qualified Control.Monad

import PrimGHC
import NanoHaskell hiding ( main )

--------------------------------------------------------------------------------

main = do
  Prelude.putStrLn "*** fuck"
  text <- Prelude.readFile "test.nano" -- NanoHaskell.hs" -- "test_readint"

  let blocks = (lexer (_fromGhcString text))
  Prelude.putStrLn ("number of top level blocks = " ++ show (length blocks))
  -- Prelude.print (_toGhcList blocks)

  let toplevs = map parseTopLevelBlock blocks
  Prelude.putStrLn "\n----------------------------------\nSYNTAX BLOCKS"
  Control.Monad.mapM_ Prelude.print (_toGhcList toplevs)

  let defins = catMaybes (map mbDefin toplevs)
  Prelude.putStrLn "\n----------------------------------\nTOPLEVEL DEFINS"
  Prelude.print (recogPrimApps (programToExpr defins))

  let dconTrie = collectDataCons (programToExpr defins)
  Prelude.putStrLn "\n----------------------------------\nCONSTURCTORS"
  Control.Monad.mapM_ Prelude.print (_toGhcList (trieToList dconTrie))

  let core = programToCore defins
  Prelude.putStrLn "\n----------------------------------\nCORE"
  Prelude.print core

  let val = eval Nil core
  Prelude.putStrLn "\n----------------------------------\nRESULT"
  Prelude.print (showValue val)

