
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
import Dependency
import Core
import ScopeCheck
import Inliner
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
{-% include "Dependency.hs" %-}
{-% include "Core.hs"       %-}
{-% include "ScopeCheck.hs" %-}
{-% include "Inliner.hs"    %-}
{-% include "Closure.hs"    %-}
{-% include "CodeGen.hs"    %-}
{-% include "Eval.hs"       %-}

--------------------------------------------------------------------------------
-- * Compiler entry point 

-- | GHC \/ nanohs shared entry point
main = runIO nanoMain 

-- | Nano entry point
nanoMain :: IO Unit
nanoMain = iobind getArgs (\args -> case args of { Nil -> printUsage ; Cons cmd args' -> handleCommand cmd args' }) where
  { handleCommand cmd args = case cmd of { Cons dash cmd1 -> ifte (cneq dash '-') printUsage (case cmd1 of { Cons c _ -> 
      ifte (ceq c 'i') (interpret     args) (
      ifte (ceq c 'c') (compile False args) ( 
      ifte (ceq c 'o') (compile True  args) printUsage)) })}
  ; interpret      args = case args of { Cons input rest -> runInterpreter input ; _ -> printUsage } 
  ; compile   flag args = case args of { Cons input rest -> case rest of { Cons output _ -> runCompiler flag input output ; _ -> printUsage } ; _ -> printUsage }}

printUsage :: IO Unit
printUsage = iomapM_ putStrLn 
  [ "usage:"
  , "./nanohs -i <input.hs>               # interpret"
  , "./nanohs -c <input.hs> <output.c>    # compile without optimizations"    
  , "./nanohs -o <input.hs> <output.c>    # compile with optimizations"     ] 

runCompiler :: Bool -> FilePath -> FilePath -> IO Unit
runCompiler optimize inputFn outputFn = iobind (loadModules inputFn) (\prgdata -> case prgdata of { 
  PrgData strlits dconTrie coreprg -> 
    iosequence_ 
      [ putStrLn (append "compiling with optimizations " (ifte optimize "enabled" "disabled"))
      , let { lprogram = coreProgramToLifted (ifte optimize (optimizeCorePrg coreprg) coreprg)
            ; code     = runCodeGenM_ (liftedProgramToCode inputFn strlits dconTrie lprogram)
            } in writeLines outputFn code 
      , putStrLn "done." ]})

runInterpreter :: FilePath -> IO Unit
runInterpreter inputFn = iobind (loadModules inputFn) (\prgdata -> case prgdata of { 
  PrgData strlits dconTrie coreprg -> case coreprg of { CorePrg blocks _mainIdx main ->
    ioseq (putStrLn "interpreting...") (let 
     { toplevs  = map definedWhat (forgetBlockStructure blocks)
     ; startEnv = Env toplevs Nil strlits
     } in printValue (eval startEnv main)) }})
    
--------------------------------------------------------------------------------
-- ** Load and parse source files

data ProgramData = PrgData (List String) DataConTable CoreProgram

loadModules :: FilePath -> IO ProgramData
loadModules inputFn =
  iobind (loadAndParse1 Nil inputFn) (\pair -> case pair of { Pair files toplevs -> (let 
      { defins0  = catMaybes (map mbDefin toplevs)
      ; dpair    = extractStringConstants defins0 } in case dpair of { Pair strlits defins1 -> let 
        { dconTrie = collectDataCons defins1
        ; program  = reorderProgram  defins1
        ; coreprg  = programToCoreProgram dconTrie program
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
  ; False -> ioseq (putStrLn (append "+ " fname)) (iobind (readFile fname) (\text -> let 
      { blocks   = lexer fname text
      ; toplevs  = map (parseTopLevelBlock fname) blocks
      ; includes = filterIncludes toplevs
      ; sofar'   = Cons fname sofar
      } in iobind (loadAndParseMany sofar' includes) (\loaded -> case loaded of { Pair sofar'' toplevs2 -> 
           ioreturn (Pair sofar'' (append toplevs toplevs2)) }))) }

--------------------------------------------------------------------------------
