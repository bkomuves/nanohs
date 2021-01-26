
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Main where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import qualified Prelude

import PrimGHC
import NanoHaskell hiding ( main )

--------------------------------------------------------------------------------

main = do
  Prelude.putStrLn "*** fuck"
  text <- Prelude.readFile "NanoHaskell.hs" -- "test_readint"

  let blocks = (lexer (_fromGhcString text))
  Prelude.print (length blocks)
  -- Prelude.print (_toGhcList blocks)

  let toplevs = map parseTopLevelBlock blocks
  -- Control.Monad.mapM_ Prelude.print (_toGhcList toplevs)

  let defins = catMaybes (map mbDefin toplevs)
  -- Prelude.print (recogPrimApps (programToExpr defins))

  let core = programToCore defins
  Prelude.print core