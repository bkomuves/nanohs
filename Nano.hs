
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
import Core
import Eval
import Parser

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "PrimOps.hs"    %-}
{-% include "DataCon.hs"    %-}
{-% include "Syntax.hs"     %-}
{-% include "Core.hs"       %-}
{-% include "Eval.hs"       %-}
{-% include "Parser.hs"     %-}

--------------------------------------------------------------------------------
-- * Config

-- targetOS :: Target
-- targetOS = MacOS

-- | Name of the entry point
nanoMainIs :: Name
nanoMainIs = "main"

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
      } in writeFile outputFn (unlines code) )})

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
   
exprToCore :: DataConTable -> Scope -> Expr -> Term
exprToCore dconTable iniScope expr = scopeCheck dconTable iniScope (recogPrimApps1 expr)

data CoreProgram 
  = CorePrg (Program Term) Term 
  deriving Show

programToCoreProgram :: Program Expr -> CoreProgram
programToCoreProgram defins = CorePrg (map worker defins) main where
  { duplicate n = concat [ "multiple declaration of " , quoteString n ]
  ; topLevScope = trieFromListUnique duplicate (zipWithIndex (\n i -> Pair n (TopL i)) (map definedName defins))
  ; dconTable   = collectDataCons defins
  ; worker def  = case def of { Defin name expr -> Defin name (exprToCore dconTable topLevScope expr) } 
  ; no_main_err = \_ -> error (concat [ "entry point " , quoteString nanoMainIs , " not found" ]) 
  ; main = case trieLookup nanoMainIs topLevScope of { Just varl -> case varl of
      { TopL k -> AtmT (VarA (Named nanoMainIs (TopV k))) ; _ -> no_main_err Unit } ; _ -> no_main_err Unit } } 

--------------------------------------------------------------------------------
-- ** Scope checking / conversion to core

data VarL 
  = LevL Level 
  | TopL Int
  deriving Show

type Scope = Trie VarL

lookupVar :: Level -> Scope -> String -> Var
lookupVar level scope name =
  case trieLookup name scope of 
    { Just v  -> case v of { LevL k -> IdxV (dec (minus level k)) ; TopL j -> TopV j } 
    ; Nothing -> error (append3 "variable name " (quoteString name) " not in scope") }

lookupCon :: DataConTable -> String -> Con
lookupCon dcontable name =
  case trieLookup name dcontable of { Just con -> con ; Nothing ->
    error (append3 "fatal error: constructor" (quoteString name) " not found") }

scopeCheck :: DataConTable -> Scope -> Expr -> Term
scopeCheck dcontable = go 0 where
  { mbAtom level scope expr =  case expr of
      { VarE  name -> case isDCon name of
        { True  -> Just (ConA (Named name (lookupCon dcontable   name)))
        ; False -> Just (VarA (Named name (lookupVar level scope name))) }
      ; LitE  lit -> case lit of
        { StrL cs -> Nothing
        ; _       -> Just (KstA lit) }
      ; _ -> Nothing } 
  ; go level scope expr = case expr of
    { VarE  name -> case mbAtom level scope expr of
        { Just atom -> AtmT atom
        ; Nothing   -> error "fatal error: VarE should be always an atom!" }
    ; StrE j     -> AtmT (VarA (Named (appendInt "str_" j) (StrV j)))
    ; AppE e1 e2 -> case mbAtom level scope e2 of
        { Just atom -> AppT (go level scope e1) atom
        ; Nothing   -> LetT (go level scope e2) (AppT (go (inc level) scope e1) (VarA (Named "letx" (IdxV 0)))) }
    ; LamE  name body -> LamT (Named name (go (inc level) (trieInsert name (LevL level) scope) body))
    ; LetE  defs body -> case defs of { Nil -> go level scope body ; Cons defin rest -> case defin of 
        { Defin name rhs -> let { tm = go level scope rhs ; scope' = trieInsert name (LevL level) scope }
                            in  LetT tm (go (inc level) scope' (LetE rest body)) } }
    ; RecE  defs body -> let { n = length defs ; level' = plus level n
        ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
        ; scope' = foldl f scope (zip (map definedName defs) (rangeFrom level n))
        } in RecT n (map (goDefin level' scope') defs) (go level' scope' body)
    ; CaseE what brs -> case mbAtom level scope what of
        { Just atom -> goCase level scope atom brs
        ; Nothing   -> LetT (go level scope what) (goCase (inc level) scope (VarA (Named "scrut" (IdxV 0))) brs) }
    ; LitE  lit -> case lit of
        { StrL cs -> go level scope (ListE (map (\x -> LitE (ChrL x)) cs))
        ; _       -> AtmT (KstA lit) }
    ; ListE exprs -> case exprs of 
        { Nil       -> AtmT (ConA (Named "Nil" con_Nil))
        ; Cons e es -> go level scope (AppE (AppE (VarE "Cons") e) (ListE es)) }
    ; PrimE prim args -> case prim of { PrimOp _arity pri -> case isLazyPrim pri of 
        { False -> goPrim prim 0 level scope Nil args 
      --  { False -> goArgs level scope args (PriT prim 
      --      (zipWithIndex (\i j -> VarA (Named (appendInt "name" j) (IdxV i))) (reverse (range (length args))) ))
        ; True  -> LZPT prim (map (go level scope) args) }}
    }
  -- ; finishPrim :: PrimOp -> List (Either Term Atom) -> Int -> Term 
  ; finishPrim prim theEis ofs = let 
      { theVars = zipWithIndex (\i j -> VarA (Named (appendInt "parg" j) (IdxV i))) (reverse (range ofs)) 
      ; worker eis vars atoms = case eis of { Nil -> PriT prim (reverse atoms) ; Cons ei eis' -> case ei of
          { Right atom -> worker eis' vars (Cons (shiftAtom ofs atom) atoms) 
          ; Left  term -> case vars of { Cons var vars' -> LetT term (worker eis' vars' (Cons var atoms)) }}}
      } in worker theEis theVars Nil
  -- ; goPrim :: PrimOp -> Int -> Level -> Scope -> List (Either Term Atom) -> List Expr -> Term 
  ; goPrim prim ofs level scope newargs oldargs = case oldargs of 
      { Nil            -> finishPrim prim (reverse newargs) ofs 
      ; Cons this rest -> case mbAtom (minus level ofs) scope this of 
        { Just atom -> goPrim prim      ofs       level  scope (Cons (Right atom                 ) newargs) rest 
        ; Nothing   -> goPrim prim (inc ofs) (inc level) scope (Cons (Left  (go level scope this)) newargs) rest }}
  -- ; goArgs level scope args body = case args of 
  --     { Nil            -> body 
  --     ; Cons this rest -> LetT (go level scope this) (goArgs (inc level) scope rest body) }
  ; goDefin level scope defin = case defin of { Defin name what -> Named name (go level scope what) }
  ; goCase level scope var branches = CasT var (map goBranch branches) where
    { goBranch branch = case branch of
        { DefaultE         rhs -> DefaultT (go level scope rhs)
        ; BranchE con args rhs -> let { n = length args ; level' = plus level n
          ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
          ; scope' = foldl f scope (zip args (rangeFrom level n))
          } in BranchT (Named con (lookupCon dcontable con)) n (go level' scope' rhs) } } }

--------------------------------------------------------------------------------
-- * The compiler
-- ** Closure conversion

-- pattern VarF nvar = AtmF (VarA nvar)
-- pattern ConF ncon = AtmF (ConA ncon)
-- pattern KstF lit  = AtmF (KstA lit )

-- | We lift all lambdas (and lets, and branch right hand sides) to top-level
data Lifted
  = AtmF Atom
  | AppF Lifted Atom
  | PriF PrimOp (List Atom  )
  | LZPF PrimOp (List Lifted)
  | CasF Atom (List BranchF)
  | LamF ClosureF
  | RecF Int (List (Named ClosureF)) Lifted
  | LetF ClosureF Lifted
  deriving Show

data BranchF
  = BranchF (Named Con) Int ClosureF
  | DefaultF ClosureF
  deriving Show

isDefaultF :: BranchF -> Bool
isDefaultF branch = case branch of { DefaultF _ -> True ; _ -> False }

hasDefaultF :: List BranchF -> Bool
hasDefaultF ls = case ls of { Nil -> False ; Cons x xs -> case isDefaultF x of { True -> True ; _ -> hasDefaultF xs }}

-- | When allocating a closure, we create a new local environment
-- by pruning the current environment. We also remember the number
-- of lambda arguments (0 = thunk)
data ClosureF = ClosureF ClosureBody (List Idx) Arity deriving Show

data ClosureBody
  = StaticBody Static
  | InlineBody Lifted
  deriving Show

closureIndex :: ClosureF -> Static
closureIndex c = case c of { ClosureF b _ _ -> case b of { StaticBody s -> s ; _ -> error "closureIndex" } }

-- | A static function is an arity (which is separated to environment
-- size + actual lambda arity) together with a lifted body
data StatFun = StatFun Arity Arity Lifted deriving Show

-- | A top-level definition is a name, a static index and a static function
data TopLev = TopLev (Named Static) StatFun deriving Show

recogLamsT :: Term -> Pair (List Name) Term
recogLamsT term = case term of
  { LamT namedBody -> case namedBody of { Named name body ->
      case recogLamsT body of { Pair names rhs -> Pair (Cons name names) rhs } }
  ; _              -> Pair Nil term }

-- recogAppsF :: Lifted -> Pair Lifted (List Lifted)
-- recogAppsF term = case term of
--   { AppF tm1 tm2 -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args tm2) }
--   ; _            -> Pair term Nil }

recogAppsF :: Lifted -> Pair Lifted (List Atom)
recogAppsF term = case term of
  { AppF tm1 v2  -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args v2) }
  ; _            -> Pair term Nil }

-- | Figure out the part of the environment used by a term.
-- Returns a set of /levels/
pruneEnvironment :: Level -> Level -> Term -> IntSet
pruneEnvironment boundary = go where
  { goAtom level atom = case atom of
    { VarA nvar -> goVar level (forgetName nvar)
    ; ConA _    -> setEmpty
    ; KstA _    -> setEmpty }
  ; goVar  level var = case var of { TopV _ -> setEmpty ; StrV _ -> setEmpty ;
      IdxV idx -> let { j = minus level (inc idx) } in ifte (lt j boundary) (setSingleton j) setEmpty }
  ; go level term = case term of
    { AtmT atom   -> goAtom level atom
    ; AppT t1 a2  -> setUnion (go level t1) (goAtom level a2)
    ; PriT _ args -> setUnions (map (goAtom level) args)
    ; LZPT _ args -> setUnions (map (go     level) args)
    ; LamT nbody  -> go (inc level) (forgetName nbody)
    ; RecT n ts t -> let { level' = plus level n }
                     in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; PrgT n ts t -> let { level' = level }
                     in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; LetT t1 t2  -> setUnion (go (inc level) t2) (go level t1)
    ; CasT v brs  -> setUnion (goAtom level v) (setUnions (map (goBranch level) brs)) }
  ; goBranch level branch = case branch of
    { BranchT _ n rhs -> go (plus level n) rhs
    ; DefaultT    rhs -> go       level    rhs } }

-- | The closure conversion monad. Note: the list is reverse order!
type ClosM a = State (List TopLev) a

-- | Take the head entry of top level lists, and add 1 to it's index
nextStatic :: ClosM Static
nextStatic = sbind sget (\list -> case list of { Nil -> sreturn 0 ; Cons toplev _ ->
  case toplev of { TopLev named _ -> case named of { Named name s -> sreturn (inc s) }}})

-- addTopLev :: TopLev -> ClosM Unit
-- addTopLev what = smodify (Cons what)

addStatFun :: Name -> StatFun -> ClosM Static
addStatFun name statfun =
  sbind nextStatic                                             (\statidx ->
  sbind (smodify (Cons (TopLev (Named name statidx) statfun))) (\_       -> sreturn statidx ))

-- | The closure environment maps original levels to pruned de Bruijn indices
-- relative to the boundary
type ClosEnv = Map Level Idx

-- | A multi-lambda
data LambdaT
  = LambdaT Int Term
  deriving Show

-- | Closure-converting a lambda results in 1) a closure allocation
-- and 2) a static function. The latter we just add to the list of
-- of compiled stuff
--
-- The name is just a name for the resulting top-level definition
-- (so debugging is easier), and the level is the level where the lambda
-- starts (the \"boundary\" level)
--
-- TODO: this has really bad complexity because it always traverses subterms
-- at each recursive calls; we should instead define subsitutions and compose
-- them...
lambdaToClosure :: Int -> Name -> Level -> LambdaT -> ClosM ClosureF
lambdaToClosure nstatic name boundary lambda = case lambda of { LambdaT nargs body ->
  let { newlevel = plus boundary nargs
      ; pruned   = pruneEnvironment boundary newlevel body
      ; npruned  = length pruned
      ; envtable = zip pruned (reverse (range npruned))
      ; pr_idxs  = map (\j -> minus boundary (inc j)) pruned
      ; replaceIdx level idx = let { j = minus level (inc idx) } in 
          ifte (ge j boundary) (IdxV idx)
            (case mapLookup j envtable of
              { Nothing -> error "lambdaToClosure: fatal error: variable not in the pruned environment"
              ; Just m  -> let { i = plus (minus level boundary) m } in IdxV i })
      ; replaceAtom level atom = case atom of 
          { VarA nvar -> case nvar of { Named name var -> case var of
            { IdxV idx -> VarA (Named name (replaceIdx level idx)) 
            ; _        -> atom }}
          ; _ -> atom }
      ; body' = transformAtom replaceAtom newlevel body
      }
  in  sbind (closureConvert nstatic name boundary newlevel body') (\statbody ->
      sbind (addStatFun name (StatFun npruned nargs statbody))    (\statidx  ->
      sreturn (ClosureF (StaticBody statidx) pr_idxs nargs))) }
-- debug name (Triple (Triple boundary nargs pruned) body body') (


termToStaticClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToStaticClosure nstatic name level tm = case recogLamsT tm of { Pair args body -> 
  lambdaToClosure nstatic name level (LambdaT (length args) body) }

termToInlineClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToInlineClosure nstatic name level tm = 
  sbind (closureConvert nstatic name 0 level tm) (\lifted ->
  sreturn (ClosureF (InlineBody lifted) Nil 0))

-- doInlineClosure :: Term -> Bool
-- doInlineClosure _ = False

doInlineClosure tm = case tm of
  { LamT _     -> False
  ; AtmT _     -> True
  ; _          -> le (termSize tm) 128 }

termToClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToClosure nstatic name level term = ifte (doInlineClosure term) 
  (termToInlineClosure nstatic name level term) 
  (termToStaticClosure nstatic name level term)

-- | The int list is the mapping from the source code top-level functions
-- to the generated code top-level functions
data LiftedProgram = LProgram (List TopLev) (List Int) Lifted deriving Show

coreProgramToLifted :: CoreProgram -> LiftedProgram
coreProgramToLifted coreprg = case coreprg of { CorePrg defins mainTerm -> let
  { nstatic = length defins  
  ; action1 = sforM defins (\defin -> case defin of { Defin name term -> sfmap closureIndex (termToStaticClosure nstatic name 0 term) })
  ; action2 = closureConvert nstatic nanoMainIs 0 0 mainTerm  
  ; action  = sliftA2 Pair action1 action2
  } in case runState action Nil of { Pair toplist pair2 -> 
         case pair2 of { Pair idxlist main -> LProgram (reverse toplist) idxlist main } } }

addPrefix :: Name -> Name -> Name
addPrefix prefix name = append3 prefix "/" name

closureConvert :: Int -> Name -> Level -> Level -> Term -> ClosM Lifted
closureConvert nstatic nameprefix boundary = go where
  { prefixed name = addPrefix nameprefix name
  -- ; goVar level idx = IdxV idx
  -- ; goAtom level atom = case atom of 
  --     { VarA named -> case named of { Named name var -> case var of
  --       { IdxV idx   -> VarA (Named name (goVar level idx)) 
  --       ; TopV top   -> VarA (Named name (TopV top)) }}
  --     ; ConA named -> ConA named
  --     ; KstA lit   -> KstA lit   }
  ; goAtom level atom = atom
  ; go level term = case term of
    { AtmT named    -> sreturn (AtmF (goAtom level named))
    ; AppT t1 a2    -> sliftA2 AppF (go level t1) (sreturn (goAtom level a2))
    ; PriT pri args -> sreturn (PriF pri  ( map  (goAtom level) args))
    ; LZPT pri args -> sfmap   (LZPF pri) (smapM (go     level) args)
    ; LamT _        -> case recogLamsT term of { Pair args body ->
                         sfmap LamF (lambdaToClosure nstatic (prefixed "lambda") level (LambdaT (length args) body)) }
    ; CasT v brs    -> sfmap (CasF (goAtom level v)) (smapM (goBranch level) brs)
    ; RecT n nts tm -> let { level' = plus level n }
                       in  sliftA2 (RecF n) (smapM (goRec1 level') nts) (go level' tm) 
    ; LetT tm body  -> sliftA2 LetF (termToClosure nstatic (prefixed "let") level tm) (go (inc level) body) } 
  ; goRec1 level named = case named of { Named name tm -> sfmap (Named name) (termToStaticClosure nstatic (prefixed name) level tm) }
  ; goBranch level br  = case br of
    { DefaultT        rhs -> sfmap (DefaultF       ) (termToClosure    nstatic (prefixed "default")      level            rhs ) 
    ; BranchT named n rhs -> sfmap (BranchF named n) (lambdaToClosure nstatic  (prefixed (nameOf named)) level (LambdaT n rhs))
    }}

--------------------------------------------------------------------------------
-- * C language code generation
-- ** Scaffoldings

type CodeLine = String

staticLabel :: Static -> String
staticLabel fun = appendInt "static_" fun

type Unique     = Int

type CodeGenM a = State (Pair Unique (List CodeLine)) a
type CodeGenM_  = CodeGenM Unit

runCodeGenM_ :: CodeGenM_ -> List CodeLine
runCodeGenM_ action = case execState action (Pair 1 Nil) of { Pair _ list -> reverse list }

freshUnique :: CodeGenM Int
freshUnique = sbind sget                       (\pair -> case pair of { Pair u code ->
              sbind (sput (Pair (inc u) code)) (\_    -> sreturn u )})

freshName :: String -> CodeGenM Name
freshName name = sbind freshUnique (\u -> sreturn (append3 name "_" (showInt u)))

freshVar :: String -> CodeGenM Name
freshVar = freshName

freshVars :: String -> Int -> CodeGenM (List Name)
freshVars prefix n = ifte (le n 0) (sreturn Nil) (sbind (freshVar prefix) (\x -> 
  sbind (freshVars prefix (dec n)) (\xs -> sreturn (Cons x xs))))

withFreshVar :: String -> (Name -> CodeGenM a) -> CodeGenM a
withFreshVar prefix action = sbind (freshVar prefix) action

withFreshVar2 :: String -> String -> (Name -> Name -> CodeGenM a) -> CodeGenM a
withFreshVar2 pf1 pf2 action = withFreshVar pf1 (\n1 -> withFreshVar pf2 (\n2 -> action n1 n2))

withFreshVar3 :: String -> String -> String -> (Name -> Name -> Name -> CodeGenM a) -> CodeGenM a
withFreshVar3 pf1 pf2 pf3 action = withFreshVar pf1 (\n1 -> withFreshVar pf2 (\n2 -> withFreshVar pf3 (\n3 -> action n1 n2 n3)))

withFreshVar4 :: String -> String -> String -> String -> (Name -> Name -> Name -> Name -> CodeGenM a) -> CodeGenM a
withFreshVar4 pf1 pf2 pf3 pf4 action = withFreshVar pf1 (\n1 -> withFreshVar pf2 (\n2 -> withFreshVar pf3 (\n3 -> withFreshVar pf4 (\n4 -> action n1 n2 n3 n4))))

withFreshVars :: String -> Int -> (List Name -> CodeGenM a) -> CodeGenM a
withFreshVars prefix n action = sbind (freshVars prefix n) action

addLine :: CodeLine -> CodeGenM_
addLine ln = smodify (\s -> case s of { Pair u code -> Pair u (Cons ln code) })

addWords :: List String -> CodeGenM_
addWords ws = addLine (concat ws)

-- "lvalue = rhs;"
addSetValue :: Name -> CodeLine -> CodeGenM_
addSetValue lvalue rhs = addWords [ lvalue , " = " , rhs , " ;" ]

-- "type lvalue = rhs;"
addDefin :: Name -> CodeLine -> CodeGenM_
addDefin lvalue rhs = addWords [ "heap_ptr " , lvalue , " = " , rhs , " ;" ]

addLines :: List CodeLine -> CodeGenM_
addLines = smapM_ addLine

--------------------------------------------------------------------------------
-- ** Top-level structure

makeStaticFunctionTables :: List TopLev -> CodeGenM_
makeStaticFunctionTables toplevs = sseq ptrs arities where
  { ptrs = ssequence_
      [ addLines [      "void *static_funptr_table[] = " ]
      , sforM_ (zipFirstRest ("  { ") ("  , ") toplevs) (\pair -> case pair of { Pair prefix toplev ->
          case toplev of { TopLev named statfun -> case named of { Named name static ->
            addWords [ prefix , "(void*)( &" , staticLabel static , " )   // " , name ] }}})
      , addLines [ "  };" ] ]
  ; arities =  ssequence_
      [ addLines [ "" , "// envsize, arity " , "int static_arity_table[] = " ]
      , sforM_ (zipFirstRest ("  { ") ("  , ") toplevs) (\pair -> case pair of { Pair prefix toplev ->
          case toplev of { TopLev named statfun -> case named of { Named name static ->
            case statfun of { StatFun envsize arity lifted ->
              addWords [ prefix , showInt envsize , " + " , showInt arity , "    // static_" , showInt static , " = " , name ] }}}})
      , addLines [ "  };"  ] ]
  }

makeDataConTable :: DataConTable -> CodeGenM_
makeDataConTable trie = let { list = mapFromList (map swap (trieToList trie)) } in ssequence_
  [ addLines [ "char *datacon_table[] = " ]
  , sforM_ (zipFirstRest ("  { ") ("  , ") list) (\pair -> 
      case pair of { Pair prefix pair2 -> case pair2 of { Pair idx name ->
        addWords [ prefix , doubleQuoteString name , "   // " , showInt idx ] }})
  , addLines [ "  };" ] ]

type StringLitTable = List String

makeStringLitTable :: StringLitTable -> CodeGenM_
makeStringLitTable list = ssequence_
  [ addLines [ "char *string_table[] = " ]
  , sforM_ (zipFirstRest ("  { ") ("  , ") list) (\pair -> 
      case pair of { Pair prefix str -> addWords [ prefix , doubleQuoteString str ] })
  , addLines [ "  };" ] ]

liftedProgramToCode :: FilePath -> StringLitTable -> DataConTable -> LiftedProgram -> CodeGenM_
liftedProgramToCode source strlits dcontable pair = case pair of { LProgram toplevs topidxs main -> 
  let { ntoplevs = length toplevs ; nfo = StatInfo topidxs } in ssequence_
    [ addLines [ "" , concat [ "#include " , doubleQuoteString "rts.c" ] ]
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , makeDataConTable dcontable
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , makeStringLitTable strlits
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , smapM_ (toplevToCode nfo) toplevs
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , makeStaticFunctionTables toplevs
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , addLines [ "int main(int argc, char **argv) {"
               , "StaticFunPointers = static_funptr_table;"
               , "StaticFunArities  = static_arity_table;" 
               , "ConstructorNames  = datacon_table;" 
               , "StaticStringTable = string_table;" ]
    , addWords [ "NStatic           = ", showInt ntoplevs , " ;   // number of static functions " ]
    , addLines [ "rts_initialize(argc,argv);" , "" , "// main" ]
    , addWords [ "printf(" , doubleQuoteString (concat [ "[source file = " , source , "]" , backslashEn ]) , ");" ]
    , sbind (liftedToCode nfo main) (\code -> withFreshVar "fresult" (\fresult -> sseq3
        (addWords [ "heap_ptr ", fresult , " = " , code , " ; " ])
        (addWords [ "// printf(" , doubleQuoteStringLn "done." , ");" ])
        (addWords [ "rts_generic_println(" , fresult , ");" ])))
    , addLines [ "exit(0);" , "}" ]
    ] }
  
-- | Sometimes we want to inline it
functionBodyToCode :: StatInfo -> StatFun -> CodeGenM Name
functionBodyToCode nfo statfun = 
  case statfun of { StatFun envsize arity lifted -> let { ntotal = plus envsize arity } in 
    withFreshVar "BP" (\bp -> sseq
      (addWords [ "stack_ptr " , bp , " = SP - ", showInt ntotal , " ;" ])
      (sbind (liftedToCode nfo lifted) (\result -> withFreshVar "final" (\fresult -> sseq3
         (addDefin fresult result)
         (addWords [ "SP = " , bp , ";   // callee cleanup " ])
         (sreturn fresult))))) }

toplevToCode :: StatInfo -> TopLev -> CodeGenM_
toplevToCode nfo toplev = case toplev of { TopLev named statfun -> case named of { Named name static ->
  case statfun of { StatFun envsize arity lifted -> let { ntotal = plus envsize arity } in ssequence_
    [ addLine ""
    , addWords [ "// static function `" , name , "` with arity = " , showInt envsize , " + " , showInt arity ]
    , addWords [ "heap_ptr " , staticLabel static , "() {" ]
    -- , debugInfoToCode name statfun
    , sbind (functionBodyToCode nfo statfun) (\fresult -> addWords [ "return (" , fresult , ");" ] )
    , addLine "}" ] }}}

debugInfoToCode name statfun = case statfun of { StatFun envsize arity lifted -> let { ntotal = plus envsize arity } in ssequence_
  [ addWords [ "printf(" , doubleQuoteStringLn "=======================" , ");" ]
  , addWords [ "printf(" , doubleQuoteStringLn name , ");" ]
  , sforM_ (range envsize) (\i -> addWords [ "rts_debug_println(" , doubleQuoteString (appendInt "env" i) , ", (heap_ptr) SP[-" , showInt ntotal , "+" , showInt i , "] );" ])
  , sforM_ (range arity  ) (\i -> addWords [ "rts_debug_println(" , doubleQuoteString (appendInt "arg" i) , ", (heap_ptr) SP[-" , showInt arity  , "+" , showInt i , "] );" ])
  ]}

--------------------------------------------------------------------------------
-- ** main code generation

-- The list of the indices in the /original/ source in the /compiled/ top-levels
data StatInfo = StatInfo (List Static) deriving Show

-- | Allocate closure and copy environment
closureToCode' :: StatInfo -> ClosureF -> CodeGenM CodeLine
closureToCode' nfo closure = case closure of { ClosureF sbody env arity -> case sbody of 
  { StaticBody static -> case env of
    { Nil -> sreturn (concat [ "static_stack[" , showInt static , "]" ])
    ; _   -> let { envsize = length env } in withFreshVar "closure" (\var -> sseq3
      (addWords [ "heap_ptr " , var , " = rts_allocate_closure(" , showInt static , "," , showInt envsize , "," , showInt arity , ");" ])
      (copyEnvironmentTo nfo "SP" var 2 env)
      (sreturn var)) }
  ; InlineBody lifted -> functionBodyToCode nfo (StatFun (length env) arity lifted)
  }}

-- | Most of the time we need to immediate evaluate thunks!
closureToCode :: StatInfo -> ClosureF -> CodeGenM CodeLine
closureToCode nfo closure = case closure of { ClosureF sbody env arity -> case sbody of
  { InlineBody _ -> closureToCode' nfo closure
  ; StaticBody _ -> ifte (gt arity 0)
      (closureToCode' nfo closure)
      (sbind (closureToCode' nfo closure) (\thunk -> withFreshVar "val" (\val -> sseq
        (addWords [ "heap_ptr " , val , " = rts_force_value( (heap_ptr)(" , thunk , ") );" ])
        (sreturn val)))) }}

--    (sforM_ (zipIndex env) (\pair -> case pair of { Pair j idx -> 
--      addWords [ var , "[" , showInt (inc2 j) , "] = (uint64_t) DE_BRUIJN(" , showInt idx , ");" ] }))
--    (sreturn var)) }}

-- case cls of { ClosureF static env arity -> 
-- -- TOOD: optimize for env = Nil
-- -- why are we not using closureToCode here??
--         let { target = concat [ pre_sp, "[", showInt j , "]" ] } in withFreshVar "tgt" (\tgt -> ssequence_ 
--           [ addWords [ target , " = (uint64_t) rts_allocate_closure( " , showInt static , " , " , showInt (length env) , " , " , showInt arity , " );" ]
--           , swhen (not (isNil env)) (addWords [ "heap_ptr " , tgt , " = (heap_ptr) " , target , ";" ])
--           , copyEnvironmentTo nfo post_sp tgt 2 env ] )}})

evalToReg :: StatInfo -> Name -> Lifted -> CodeGenM Name
evalToReg nfo name term = withFreshVar name (\var -> sbind (liftedToCode nfo term) (\res -> sseq
  (addWords [ "heap_ptr " , var , " = " , res , ";"]) (sreturn var)))

-- does not force thunks
loadVar' ::  StatInfo -> Var -> CodeLine
loadVar' nfo var = case var of
  { IdxV i -> concat [ "DE_BRUIJN(" , showInt i , ")" ]
  ; TopV j -> case nfo of { StatInfo idxlist -> concat [ "(heap_ptr) static_stack[" , showInt (index j idxlist) , "]" ] }
  ; StrV j -> concat [ "rts_marshal_from_cstring( StaticStringTable[" , showInt j , "] )" ] }

-- forces thunks
loadVar ::  StatInfo -> Var -> CodeLine
loadVar nfo var = case var of
  { IdxV i -> concat [ "rts_force_thunk_at( SP - " , showInt (inc i) , ")" ]
  ; TopV j -> case nfo of { StatInfo idxlist -> concat [ "rts_force_thunk_at( static_stack + " , showInt (index j idxlist) , ")" ] }
  ; StrV j -> concat [ "rts_marshal_from_cstring( StaticStringTable[" , showInt j , "] )" ] }

loadAtom :: StatInfo -> Atom -> CodeLine
loadAtom nfo atom = case atom of
  { VarA named -> case named of { Named name var -> loadVar nfo var }
  ; ConA named -> case named of { Named name con -> concat [ "NULLARY_CON(" , showInt con , ")" ] }
  ; KstA lit -> case lit of
      { IntL k -> concat [ "INT_LITERAL(" , showInt k       , ")" ]
      ; ChrL c -> concat [ "CHR_LITERAL(" , showInt (ord c) , ")" ]
      ; _      -> error "codegen: unimplemented literal constant"    } }

liftedToCode :: StatInfo -> Lifted -> CodeGenM CodeLine
liftedToCode nfo lifted = case lifted of
  { AtmF atom         -> sreturn (loadAtom nfo atom)
  ; LZPF primop args  -> case primop of { PrimOp _arity prim -> lazyPrimToCode nfo prim args }
  ; PriF primop args  -> case primop of { PrimOp _arity prim -> 
      sreturn (concat [ "prim_" , showPrim prim , "(" , intercalate "," (map (loadAtom nfo) args) , ")" ])}
  ; CasF var branches -> caseOfToCode nfo var branches
  ; LamF body         -> closureToCode nfo body
  ; AppF _ _          -> case recogAppsF lifted of { Pair fun args -> applicationToCode nfo fun args }
  ; RecF n closs body -> letrecToCode nfo n (map forgetName closs) body
  ; LetF   clos  body -> letToCode nfo clos body
  }

lazyPrimToCode :: StatInfo -> Prim -> List Lifted -> CodeGenM Name
lazyPrimToCode nfo prim args = case prim of
  { Or   -> binary  args (\arg1 arg2 -> withFreshVar "res_or"    (\fres -> 
              sbind (addWords [ "heap_ptr " , fres , ";" ])      (\_    -> 
              sbind (liftedToCode nfo arg1)                      (\res1 -> 
              sbind (addWords [ "if TO_BOOL(" , res1 , ") { " , fres , " = " , res1 , "; } else { " ]) (\_ -> 
              sbind (liftedToCode nfo arg2)                      (\res2 -> 
              sbind (addWords [ fres , " = " , res2 , "; } "])   (\_ -> sreturn fres)))))))
  ; And  -> binary  args (\arg1 arg2 -> withFreshVar "res_and"   (\fres -> 
              sbind (addWords [ "heap_ptr " , fres , ";" ])      (\_    -> 
              sbind (liftedToCode nfo arg1)                      (\res1 -> 
              sbind (addWords [ "if TO_BOOL(" , res1 , ") { " ]) (\_    -> 
              sbind (liftedToCode nfo arg2)                      (\res2 -> 
              sbind (addWords [ fres , " = " , res2 , "; } else { " , fres , " = " , res1 , "; } "])  (\_ -> sreturn fres)))))))
  ; IFTE -> ternary args (\barg arg1 arg2 -> withFreshVar "res_if"    (\fres ->
              sbind (addWords [ "heap_ptr " , fres , ";" ])           (\_    -> 
              sbind (liftedToCode nfo barg)                           (\bres -> 
              sbind (addWords [ "if TO_BOOL(" , bres , ") { " ])      (\_    -> 
              sbind (liftedToCode nfo arg1)                           (\res1 -> 
              sbind (addWords [ fres , " = " , res1 , "; } else { "]) (\_    -> 
              sbind (liftedToCode nfo arg2)                           (\res2 -> 
              sbind (addWords [ fres , " = " , res2 , "; }" ])        (\_ -> sreturn fres)))))))))
  ; _    -> error "unimplemented lazy primop" }

letToCode :: StatInfo -> ClosureF -> Lifted -> CodeGenM Name
letToCode nfo cls body = 
  withFreshVar2 "loc" "obj"         (\loc obj -> 
  sbind (addLine  "// let ")        (\_    -> 
  sbind (closureToCode nfo cls)     (\val1 -> 
  sbind (addWords [ "stack_ptr " , loc  , " = rts_stack_allocate(1);" ]) (\_ ->
  sbind (addWords [ loc  , "[0] = (uint64_t) " , val1 , ";" ]) (\_ ->
  sbind (evalToReg nfo "body" body) (\res -> 
  sbind (addDefin obj res)          (\_   ->    
  sbind (addWords [ "SP = " , loc , ";" ]) (\_ -> 
  sreturn obj ))))))))

letrecToCode :: StatInfo -> Int -> List ClosureF -> Lifted -> CodeGenM Name
letrecToCode nfo n cls_list body = withFreshVar3 "obj" "pre_sp" "post_sp" (\obj pre_sp post_sp -> 
  sseq (ssequence_
    [ addWords [ "// letrec " , showInt n ]
    , addWords [ "stack_ptr " , pre_sp  , " = rts_stack_allocate(" , showInt n , ");" ]
    , addWords [ "stack_ptr " , post_sp , " = SP;" ]
    -- we fill it up with non-gc-refs, so that when allocation below triggers GC, it doesn't point to random places...
    , addWords [ "for(int i=0;i<" , showInt n , ";i++) { " , pre_sp , "[i] = (uint64_t) INT_LITERAL(0); }" ]  
    -- allocate closures
    , sforM_ (zipIndex cls_list) (\pair -> case pair of { Pair j cls -> case cls of { ClosureF cbody env arity ->
        case cbody of 
          { InlineBody lifted -> sbind (functionBodyToCode nfo (StatFun (length env) arity lifted)) (\res ->
             addWords [ pre_sp, "[", showInt j , "] = (uint64_t) (" , res , " );" ]) 
          ; StaticBody static -> case env of
             { Nil -> addWords [ pre_sp, "[", showInt j , "] = static_stack[" , showInt static , "];" ] 
             ; _   -> let { envsize = length env } in 
                addWords [  pre_sp, "[", showInt j , "] = (uint64_t) rts_allocate_closure(" , showInt static , "," , showInt envsize , "," , showInt arity , ");" ] 
             }}}})
    -- fill environments (we need to this _after_ all the allocation!)
    , sforM_ (zipIndex cls_list) (\pair -> case pair of { Pair j cls -> case cls of { ClosureF cbody env arity ->
        case cbody of 
          { InlineBody _ -> sreturn Unit
          ; StaticBody _ -> case env of { Nil -> sreturn Unit ; _ -> withFreshVar "tgt" (\tgt -> sseq
              (addDefin tgt (concat [ "(heap_ptr) " , pre_sp , "[", showInt j , "]" ]))
              (copyEnvironmentTo nfo "SP" tgt 2 env) )} }}})
    -- evaluate thunks
    , sforM_ (zipIndex cls_list) (\pair -> case pair of { Pair j cls -> case cls of {
        ClosureF static env arity -> let { i = minus n (inc j) } in swhen (eq arity 0) 
          (addWords [ "rts_force_thunk_at( " , pre_sp, " + ", showInt j , " );" ]) }})
    , sbind (evalToReg nfo "body" body) (\res -> addDefin obj res)   
    , addWords [ "SP = " , pre_sp , ";" ]
    ]) (sreturn obj))

-- NB: heap constructor tag should be compatible with the nullary constructor tag
caseOfToCode :: StatInfo -> Atom -> List BranchF -> CodeGenM Name
caseOfToCode nfo atom branches = 
  sbind (freshVar "tagword"  ) (\tagword   -> 
  sbind (freshVar "result"   ) (\result    -> 
  sbind (freshVar "scrutinee") (\scrutinee -> 
  sbind (freshVar "oldsp"    ) (\oldsp     -> 
  sbind (ssequence_ 
    [ addWords [ "// case " , prettyAtom atom , " of" ]
    , addWords [ "stack_ptr " , oldsp , " = SP ;" ]
    , addWords [ "uint64_t  " , tagword , ";" ]
    , addWords [ "heap_ptr  " , result  , ";" ]
    , addWords [ "heap_ptr  " , scrutinee , " = " , loadAtom nfo atom , ";" ]
    , addWords [ "if IS_HEAP_PTR(" , scrutinee, ") " , tagword , " = " , scrutinee , "[0]; else " , tagword , " = (intptr_t)" , scrutinee , " ;" ]
    , addWords [ "switch(" , tagword , ") {" ]
    , smapM_ (worker result scrutinee) branches
    , swhen (not (hasDefaultF branches)) 
        (addWords [ "default: rts_internal_error(" , doubleQuoteString "non-exhaustive patterns in case" , ");" ])
    , addLine  "}"
    , addWords [ "SP = " , oldsp , " ;   // branches allocate ?! " ]
    ]) (\_ -> sreturn result )))))
  where 
    { worker result scrutinee branch = case branch of
        { DefaultF closure -> ssequence_
            [ addLine "default: {" 
            , sbind (closureToCode nfo closure) (\res -> addSetValue result res) 
            , addLine "break; }" ]
        ; BranchF namedcon arity closure -> case namedcon of { Named cname con -> withFreshVar2 "env" "args" (\envptr args -> 
            case closure of { ClosureF cbody env arity -> ssequence_
              [ addWords [ "case TAGWORD_DATACON(" , showInt con , "," , showInt arity , "): {    // " , cname , "/" , showInt arity ]
              , case cbody of
                  { InlineBody _ -> sreturn Unit
                  ; StaticBody _ -> swhen (not (isNil env)) (sseq 
                      (addWords [ "stack_ptr " , envptr , " =  rts_stack_allocate(" , showInt (length env) , ");" ])
                      (copyEnvironmentTo nfo envptr envptr 0 env)) }
              , swhen (gt arity 0) (ssequence_
                  [ addWords [ "stack_ptr " , args , " = rts_stack_allocate(" , showInt arity , ");" ]
                  , sforM_ (range arity) (\j -> addWords [ args , "[" , showInt j , "] = " , scrutinee , "[" , showInt (inc j) , "];" ])
                  ])
              , case cbody of
                  { InlineBody lifted -> sbind (liftedToCode nfo lifted) (\res -> addSetValue result res)
                  ; StaticBody static -> sbind (callStatic static      ) (\res -> addSetValue result res) }
              , addLine "break; }" ] } ) }}}

--------------------------------------------------------------------------------
-- ** application

copyEnvironmentTo' :: StatInfo -> Name -> Name -> Int -> List Atom -> CodeGenM_
copyEnvironmentTo' nfo from target ofs env = sforM_ (zipIndex env) (\pair -> case pair of { Pair j atom -> 
  let { setTarget = concat [ target , "[" , showInt (plus j ofs) , "] = (uint64_t) " ] } 
  in  case atom of
    { VarA nvar -> case nvar of { Named name var -> case var of  
      { IdxV idx  -> addWords [ setTarget , "DE_BRUIJN_FROM(" , from , "," , showInt idx , ");    // " , name ] 
      ; TopV stat -> addWords [ setTarget , loadVar nfo var , " ;    // " , name ] }}
    ; _ -> addWords [ setTarget , loadAtom nfo atom , ";"] }})

idxToAtom :: String -> Idx -> Atom
idxToAtom name i = VarA (Named name (IdxV i))

copyEnvironmentTo :: StatInfo -> Name -> Name -> Int -> List Idx -> CodeGenM_
copyEnvironmentTo nfo from target ofs env = copyEnvironmentTo' nfo from target ofs (map (idxToAtom "xxx") env)

-- copy environment, then copy args, assembling these on the stack
assembleClosureArgs' :: StatInfo -> List Idx -> List Atom -> CodeGenM Name
assembleClosureArgs' nfo env args = let { envsize = length env ; nargs = length args ; ntotal = plus envsize nargs } in 
  ifte (eq ntotal 0) (sreturn "NULL") 
  ( withFreshVar "loc" (\loc -> sseq (ssequence_
    [ addWords [ "stack_ptr " , loc , " = rts_stack_allocate(" , showInt ntotal , ");" ]
    , copyEnvironmentTo  nfo loc loc 0       env
    , copyEnvironmentTo' nfo loc loc envsize args 
    ]) (sreturn loc) ))

assembleClosureArgs :: StatInfo -> List Idx -> List Idx -> CodeGenM Name
assembleClosureArgs nfo env args = assembleClosureArgs' nfo env (map (idxToAtom "xxx") args)

genericApplicationTo :: StatInfo -> Name -> List Atom -> CodeGenM Name
genericApplicationTo nfo funvar args = let { nargs = length args } in 
  withFreshVar "fresult"                    (\finalres -> 
  sbind (assembleClosureArgs' nfo Nil args) (\tmp      ->
  sbind (addWords [ "heap_ptr " , finalres , " = rts_apply( " , funvar , " , " , showInt nargs , " );" ]) (\_ ->
  sbind (addWords [ "// SP = " , tmp , ";   // callee cleans up" ]) 
        (\_ -> (sreturn finalres) ))))

callStatic :: Static -> CodeGenM Name
callStatic sidx = withFreshVar "result" (\var -> sseq
  (addWords [ "heap_ptr " , var , " = " , staticLabel sidx , "(); " ])
  (sreturn var))

callClosureBody :: StatInfo -> ClosureF -> CodeGenM Name
callClosureBody nfo closure = case closure of { ClosureF cbody env arity -> case cbody of
  { StaticBody static -> callStatic static
  ; InlineBody lifted -> functionBodyToCode nfo (StatFun (length env) arity lifted) }}

applyClosure :: StatInfo -> ClosureF -> List Atom -> CodeGenM CodeLine
applyClosure nfo closure args = case closure of { ClosureF cbody env fun_arity -> 
  let { nargs = length args ; envsize = length env ; ntotal = plus envsize fun_arity } in case compare nargs fun_arity of
    { EQ -> sbind (assembleClosureArgs' nfo env args) (\tmp -> callClosureBody nfo closure)
    ; GT -> sbind (assembleClosureArgs' nfo env (take fun_arity args)) (\tmp    -> 
            sbind (callClosureBody nfo closure)                        (\funres -> 
                  (genericApplicationTo nfo funres (drop fun_arity args))))
    ; LT -> case cbody of
        { InlineBody _      -> error "applyClosure: underapplication of inlined closure ?!?"
        ; StaticBody static -> withFreshVar "obj" (\obj -> sseq (ssequence_
              [ addWords [ "heap_ptr ", obj , " = rts_allocate_closure( " , showInt static , " , " , showInt ntotal , " , " , showInt (minus fun_arity nargs) , " );" ]
              , copyEnvironmentTo  nfo "SP" obj     2          env
              , copyEnvironmentTo' nfo "SP" obj (inc2 envsize) args 
              ]) (sreturn obj)) } } }

applicationToCode :: StatInfo -> Lifted -> List Atom -> CodeGenM CodeLine
applicationToCode nfo fun args = case args of { Nil -> liftedToCode nfo fun ; _ -> case fun of
  { LamF closure -> applyClosure nfo closure args
  ; AtmF atom    -> case atom of
    { ConA named   -> let { nargs = length args} in case named of { Named dcon_name con -> withFreshVar "obj" (\obj -> sseq (ssequence_
        [ addWords [ "heap_ptr ", obj , " = rts_allocate_datacon(" , showInt con , "," , showInt nargs , ");   // " , dcon_name , "/" , showInt nargs]
        , copyEnvironmentTo' nfo "SP" obj 1 args
        ]) (sreturn obj)) }
    ; _ -> sbind (evalToReg nfo "fun" fun) (\funvar -> genericApplicationTo nfo funvar args) }
  ; _   -> sbind (evalToReg nfo "fun" fun) (\funvar -> genericApplicationTo nfo funvar args) }}

--------------------------------------------------------------------------------
