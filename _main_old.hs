
{-# LANGUAGE NoImplicitPrelude, MagicHash  #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Main where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show(..) , (++) , (.) , ($)  )
import qualified Prelude

import qualified Control.Monad

import System.Environment

import PrimGHC

import Nano hiding ( main )

import Base 
import Containers
import Types
import PrimOps
import DataCon
import Syntax
import Parser
import Dependency
import Core
import ScopeCheck
import Inliner
import Closure
import CodeGen

import qualified Text.Show.Pretty as Pretty

--------------------------------------------------------------------------------

myPrettyTermDefin :: Prelude.String -> Defin Term -> Prelude.IO ()
myPrettyTermDefin prefix (Defin n t) = Prelude.putStrLn (Prelude.concat list) where
  list = [ prefix , _toGhcString n , " := " , _toGhcString (showTerm t) ] :: [Prelude.String]

myPrettyTermBlock :: Block Term -> Prelude.IO ()
myPrettyTermBlock (NonRecursive def) =                      myPrettyTermDefin "- "   def
myPrettyTermBlock (Recursive defs  ) = Control.Monad.mapM_ (myPrettyTermDefin "> ") (_toGhcList defs)


main = do
  Prelude.putStrLn "*** main.hs"
  args <- System.Environment.getArgs
  case args of
    [] -> error "usage: runghc main.hs <inputfile>"
    (fn:_) -> compile fn

-- type Files  = List FilePath
-- type Loaded = Pair Files (List TopLevel)
-- 
-- loadAndParseMany :: Files -> List FilePath -> IO Loaded
-- loadAndParseMany sofar fnames = case fnames of { Nil -> ioreturn (Pair sofar Nil) ; Cons this rest ->
--   iobind (loadAndParse1    sofar  this) (\loaded -> case loaded of { Pair sofar'  toplevs1 ->
--   iobind (loadAndParseMany sofar' rest) (\loaded -> case loaded of { Pair sofar'' toplevs2 ->
--   ioreturn (Pair sofar'' (append toplevs1 toplevs2)) }) }) }
-- 
-- loadAndParse1 :: Files -> FilePath -> IO Loaded
-- loadAndParse1 sofar fname = case stringMember fname sofar of
--   { True  -> ioreturn (Pair sofar Nil)
--   ; False -> iobind (readFile fname) (\text -> ioseq (putStrLn (append "+ " fname)) (let 
--       { blocks   = lexer fname text
--       ; toplevs  = map (parseTopLevelBlock fname) blocks
--       ; includes = filterIncludes toplevs
--       ; sofar'   = Cons fname sofar
--       } in iobind (loadAndParseMany sofar' includes) (\loaded -> case loaded of { Pair sofar'' toplevs2 -> 
--            ioreturn (Pair sofar'' (append toplevs toplevs2)) }))) }

compile fname = do
  let source = (_fromGhcString fname)

--  text <- Prelude.readFile fname
--
--  let blocks = (lexer source (_fromGhcString text))
--  Prelude.putStrLn ("number of top level blocks = " ++ show (length blocks))
--  -- Prelude.print (_toGhcList blocks)
--
--  let toplevs = map (parseTopLevelBlock source) blocks
----  Prelude.putStrLn "\n----------------------------------\nSYNTAX BLOCKS"
----  Control.Monad.mapM_ Prelude.print (_toGhcList toplevs)

  loaded <- runIO (loadAndParse1 Nil source)
  let toplevs = snd loaded

  let defins0 = catMaybes (map mbDefin toplevs)
  let Pair strlits defins1 = extractStringConstants defins0
  Prelude.putStrLn "\n----------------------------------\nTOPLEVEL DEFINS"
  Control.Monad.mapM_ Prelude.print (_toGhcList (recogPrimApps defins1))

  let dconTrie = collectDataCons defins1
  Prelude.putStrLn "\n----------------------------------\nCONSTRUCTORS"
  Control.Monad.mapM_ Prelude.print (_toGhcList (trieToList dconTrie))

  let blocks = reorderProgram defins1
  Prelude.putStrLn "\n----------------------------------\nREORDERED TOPLEVEL DEFINS"
  Control.Monad.mapM_ Prelude.print (_toGhcList blocks)

  let coreprg@(CorePrg coredefs mainIdx mainTerm) = programToCoreProgram dconTrie blocks
  Prelude.putStrLn "\n----------------------------------\nCORE"
  Control.Monad.mapM_ myPrettyTermBlock (_toGhcList coredefs)
  Prelude.print (mainIdx,mainTerm)

  -- let coreprg'@(CorePrg coredefs' mainIdx' mainTerm') = inlineCorePrg 24 coreprg
  let coreprg'@(CorePrg coredefs' mainIdx' mainTerm') = optimizeCorePrg coreprg
  Prelude.putStrLn "\n----------------------------------\nOPTIMIZED CORE"
  Control.Monad.mapM_ myPrettyTermBlock (_toGhcList coredefs')
  Prelude.print (mainIdx',mainTerm')


  let lprogram = coreProgramToLifted coreprg'
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

