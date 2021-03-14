
-- | C language code generation

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module CodeGen where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
import PrimOps
-- import DataCon
import Core
import Closure

{-% include "Base.hs"       %-}
{-% include "Containers.hs" %-}
{-% include "Types.hs"      %-}
{-% include "PrimOps.hs"    %-}
-- {-% include "DataCon.hs"    %-}
{-% include "Core.hs"       %-}
{-% include "Closure.hs"    %-}

--------------------------------------------------------------------------------
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
  , case list of { Nil -> addLine "  {" ; _ ->
      sforM_ (zipFirstRest ("  { ") ("  , ") list) (\pair -> 
        case pair of { Pair prefix pair2 -> case pair2 of { Pair idx name ->
          addWords [ prefix , doubleQuoteString name , "   // " , showInt idx ] }}) }
  , addLines [ "  };" ] ]

type StringLitTable = List String

makeStringLitTable :: StringLitTable -> CodeGenM_
makeStringLitTable list = ssequence_
  [ addLines [ "char *string_table[] = " ]
  , case list of { Nil -> addLine "  {" ; _ ->
      sforM_ (zipFirstRest ("  { ") ("  , ") list) (\pair -> 
        case pair of { Pair prefix str -> addWords [ prefix , doubleQuoteString str ] }) }
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

--------------------------------------------------------------------------------
  
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
  , sforM_ (range arity  ) (\i -> addWords [ "rts_debug_println(" , doubleQuoteString (appendInt "arg" (minus arity   (inc i))) , ", (heap_ptr) SP[-" , showInt ntotal  , "+" , showInt i , "] );" ])
  , sforM_ (range envsize) (\i -> addWords [ "rts_debug_println(" , doubleQuoteString (appendInt "env" (minus envsize (inc i))) , ", (heap_ptr) SP[-" , showInt envsize , "+" , showInt i , "] );" ])
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
      (copyEnvironmentTo nfo "SP" var 1 env)
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
              (copyEnvironmentTo nfo "SP" tgt 1 env) )} }}})
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
        ; BranchF namedcon arity closure -> case namedcon of { Named cname con -> withFreshVar3 "env" "args" "base" (\envptr args base -> 
            case closure of { ClosureF cbody env arity -> ssequence_
              [ addWords [ "case TAGWORD_DATACON(" , showInt con , "," , showInt arity , "): {    // " , cname , "/" , showInt arity ]
              , addWords [ "stack_ptr " , base , " = SP;" ]
              , swhen (gt arity 0) (ssequence_
                  [ addWords [ "stack_ptr " , args , " = rts_stack_allocate(" , showInt arity , ");" ]
                  , sforM_ (range arity) (\j -> addWords [ args , "[" , showInt (minus arity (inc j)) , "] = " , scrutinee , "[" , showInt (inc j) , "];" ])
                  ])
              , case cbody of
                  { InlineBody _ -> sreturn Unit
                  ; StaticBody _ -> swhen (not (isNil env)) (sseq 
                      (addWords [ "stack_ptr " , envptr , " =  rts_stack_allocate(" , showInt (length env) , ");" ])
                      (copyEnvironmentTo nfo base envptr 0 env)) }
              , case cbody of
                  { InlineBody lifted -> sbind (liftedToCode nfo lifted) (\res -> addSetValue result res)
                  ; StaticBody static -> sbind (callStatic static      ) (\res -> addSetValue result res) }
              , addLine "break; }" ] } ) }}}

--------------------------------------------------------------------------------
-- ** application

-- | Note the `reverse` - we put everything in reverse order to the stack!
copyEnvironmentTo' :: StatInfo -> Name -> Name -> Int -> List Atom -> CodeGenM_
copyEnvironmentTo' nfo from target ofs env = sforM_ (zipIndex (reverse env)) (\pair -> case pair of { Pair j atom -> 
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

-- copy the args, then copy the environment (everything is in reverse oreder), assembling these on the stack
assembleClosureArgs' :: StatInfo -> List Idx -> List Atom -> CodeGenM Name
assembleClosureArgs' nfo env args = let { envsize = length env ; nargs = length args ; ntotal = plus envsize nargs } in 
  ifte (eq ntotal 0) (sreturn "NULL") 
  ( withFreshVar "loc" (\loc -> sseq (ssequence_
    [ addWords [ "stack_ptr " , loc , " = rts_stack_allocate(" , showInt ntotal , ");" ]
    , copyEnvironmentTo' nfo loc loc 0     args
    , copyEnvironmentTo  nfo loc loc nargs env 
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
        { InlineBody _      -> error "applyClosure: underapplication of inlined closure (?!?)"
        ; StaticBody static -> withFreshVar "obj" (\obj -> sseq (ssequence_
              [ addWords [ "heap_ptr ", obj , " = rts_allocate_closure( " , showInt static , " , " , showInt ntotal , " , " , showInt (minus fun_arity nargs) , " );" ]
              , copyEnvironmentTo' nfo "SP" obj  1          args
              , copyEnvironmentTo  nfo "SP" obj (inc nargs) env 
              ]) (sreturn obj)) } } }

applicationToCode :: StatInfo -> Lifted -> List Atom -> CodeGenM CodeLine
applicationToCode nfo fun args = case args of { Nil -> liftedToCode nfo fun ; _ -> case fun of
  { LamF closure -> applyClosure nfo closure args
  ; AtmF atom    -> case atom of
    { ConA named   -> let { nargs = length args} in case named of { Named dcon_name con -> withFreshVar "obj" (\obj -> sseq (ssequence_
        [ addWords [ "heap_ptr ", obj , " = rts_allocate_datacon(" , showInt con , "," , showInt nargs , ");   // " , dcon_name , "/" , showInt nargs]
        , copyEnvironmentTo' nfo "SP" obj 1 (reverse args)
        ]) (sreturn obj)) }
    ; _ -> sbind (evalToReg nfo "afun" fun) (\funvar -> genericApplicationTo nfo funvar args) }
  ; _   -> sbind (evalToReg nfo "gfun" fun) (\funvar -> genericApplicationTo nfo funvar args) }}

--------------------------------------------------------------------------------