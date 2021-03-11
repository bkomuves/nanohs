
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Main where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show(..) , (++) , (.) , ($) )
import qualified Prelude

import qualified Control.Monad

import System.Environment

import PrimGHC

import Nano hiding ( main )

import Base 
import Types
import PrimOps
import DataCon
import Syntax
import Parser

--------------------------------------------------------------------------------

main = do
  Prelude.putStrLn "*** main.hs"
  args <- System.Environment.getArgs
  case args of
    [] -> error "usage: runghc main.hs <inputfile>"
    (fn:_) -> compile fn

compile fname = do
  text <- Prelude.readFile fname
  let source = (_fromGhcString fname)

  let blocks = (lexer source (_fromGhcString text))
  Prelude.putStrLn ("number of top level blocks = " ++ show (length blocks))
  -- Prelude.print (_toGhcList blocks)

  let toplevs = map (parseTopLevelBlock source) blocks
--  Prelude.putStrLn "\n----------------------------------\nSYNTAX BLOCKS"
--  Control.Monad.mapM_ Prelude.print (_toGhcList toplevs)

  let defins0 = catMaybes (map mbDefin toplevs)
  let Pair strlits defins = extractStringConstants defins0
  Prelude.putStrLn "\n----------------------------------\nTOPLEVEL DEFINS"
  Control.Monad.mapM_ Prelude.print (_toGhcList (recogPrimApps defins))


  let dconTrie = collectDataCons defins
--  Prelude.putStrLn "\n----------------------------------\nCONSTURCTORS"
--  Control.Monad.mapM_ Prelude.print (_toGhcList (trieToList dconTrie))

  let coreprg@(CorePrg coredefs mainTerm) = programToCoreProgram defins
  Prelude.putStrLn "\n----------------------------------\nCORE"
  Control.Monad.mapM_ Prelude.print (_toGhcList coredefs)
  Prelude.print mainTerm

  let lprogram = coreProgramToLifted coreprg
      LProgram statfuns topidxs lmain = lprogram
  Prelude.putStrLn "\n----------------------------------\nLIFTED"
  Control.Monad.mapM_ Prelude.print (_toGhcList statfuns)
  Prelude.print lmain
  -- Prelude.print topidxs

  let code = runCodeGenM_ (liftedProgramToCode source strlits dconTrie lprogram)
  -- Prelude.putStrLn "\n----------------------------------\nASM"
  -- Control.Monad.mapM_ (Prelude.putStrLn . _toGhcString) (_toGhcList asm)
  Prelude.writeFile "tmp.c" (Prelude.unlines $ Prelude.map _toGhcString $ _toGhcList code)

  -- let val = eval Nil core
  -- Prelude.putStrLn "\n----------------------------------\nINTEPRETED RESULT"
  -- Prelude.print (showValue val)

