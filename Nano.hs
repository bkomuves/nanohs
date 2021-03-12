
-- | The compiler main module
--

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Nano where

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
import Parser
import Core
import ScopeCheck
import Closure
import CodeGen
import Eval

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "PrimOps.hs"    %-}
{-% include "DataCon.hs"    %-}
{-% include "Syntax.hs"     %-}
{-% include "Parser.hs"     %-}
{-% include "Core.hs"       %-}
{-% include "ScopeCheck.hs" %-}
{-% include "Closure.hs"    %-}
{-% include "CodeGen.hs"    %-}
{-% include "Eval.hs"       %-}

--------------------------------------------------------------------------------
-- * Compiler entry point 

-- | GHC \/ nanohs shared entry point
main = runIO# nanoMain 

-- | Nano entry point
nanoMain :: IO Unit
nanoMain = iobind getArgs (\args -> case args of { Nil -> printUsage ; Cons cmd args' -> handleCommand cmd args' }) where
  { handleCommand cmd args = case cmd of { Cons dash cmd1 -> ifte (cneq dash '-') printUsage (case cmd1 of { Cons c _ -> 
      ifte (ceq c 'i') (interpret args) (ifte (ceq c 'c') (compile args) printUsage) })}
  ; interpret args = case args of { Cons input rest -> runInterpreter input ; _ -> printUsage } 
  ; compile   args = case args of { Cons input rest -> case rest of { Cons output _ -> runCompiler input output ; _ -> printUsage } ; _ -> printUsage }}

printUsage :: IO Unit
printUsage = iomapM_ putStrLn 
  [ "usage:"
  , "./nanohs -i <input.hs>               # interpret"
  , "./nanohs -c <input.hs> <output.c>    # compile"   ] 

runCompiler :: FilePath -> FilePath -> IO Unit
runCompiler inputFn outputFn = iobind (loadModules inputFn) (\prgdata -> case prgdata of { 
  PrgData strlits dconTrie coreprg -> 
    ioseq (putStrLn "compiling...") (let
      { lprogram = coreProgramToLifted coreprg
      ; code     = runCodeGenM_ (liftedProgramToCode inputFn strlits dconTrie lprogram)
      } in writeLines outputFn code )})

runInterpreter :: FilePath -> IO Unit
runInterpreter inputFn = iobind (loadModules inputFn) (\prgdata -> case prgdata of { 
  PrgData strlits dconTrie coreprg -> case coreprg of { CorePrg defins main ->
    ioseq (putStrLn "interpreting...") (let 
     { toplevs  = map definedWhat defins
     ; startEnv = Env toplevs Nil strlits
     } in printValue (eval startEnv main)) }})
    
--------------------------------------------------------------------------------
-- ** Load and parse source files

data ProgramData = PrgData (List String) DataConTable CoreProgram

loadModules :: FilePath -> IO ProgramData
loadModules inputFn =
  iobind (loadAndParse1 Nil inputFn) (\pair -> case pair of { Pair files toplevs -> (let 
      { defins0  = catMaybes (map mbDefin toplevs)
      ; dpair    = extractStringConstants defins0 } in case dpair of { Pair strlits defins -> let 
        { dconTrie = collectDataCons defins
        ; coreprg  = programToCoreProgram defins
        } in ioreturn (PrgData strlits dconTrie coreprg) })}) 

type Files  = List FilePath
type Loaded = Pair Files (List TopLevel)

loadAndParseMany :: Files -> List FilePath -> IO Loaded
loadAndParseMany sofar fnames = case fnames of { Nil -> ioreturn (Pair sofar Nil) ; Cons this rest ->
  iobind (loadAndParse1    sofar  this) (\loaded -> case loaded of { Pair sofar'  toplevs1 ->
  iobind (loadAndParseMany sofar' rest) (\loaded -> case loaded of { Pair sofar'' toplevs2 ->
  ioreturn (Pair sofar'' (append toplevs1 toplevs2)) }) }) }

loadAndParse1 :: Files -> FilePath -> IO Loaded
loadAndParse1 sofar fname = case stringMember fname sofar of
  { True  -> ioreturn (Pair sofar Nil)
  ; False -> iobind (readFile fname) (\text -> ioseq (putStrLn (append "+ " fname)) (let 
      { blocks   = lexer fname text
      ; toplevs  = map (parseTopLevelBlock fname) blocks
      ; includes = filterIncludes toplevs
      ; sofar'   = Cons fname sofar
      } in iobind (loadAndParseMany sofar' includes) (\loaded -> case loaded of { Pair sofar'' toplevs2 -> 
           ioreturn (Pair sofar'' (append toplevs toplevs2)) }))) }

--------------------------------------------------------------------------------
