
-- | Dependency analysis: Partitioning lets into recursive and non-recursive parts

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Dependency where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers
import Types
-- import Core
import Syntax

{-% include "Base.hs"        %-}
{-% include "Containers.hs"  %-}
{-% include "Types.hs"       %-}
-- {-% include "Core.hs"        %-}
{-% include "Syntax.hs"      %-}

--------------------------------------------------------------------------------
-- * partition lets into recursive and non-recursive parts

data Let
  = Let1   LDefinE
  | LetRec (List LDefinE)
  deriving Show

isRecursiveDefin :: DefinE -> Bool
isRecursiveDefin def = case def of { Defin name rhs -> trieMember name (exprFreeVars rhs) }

mkLet :: List LDefinE -> Let
mkLet list = case mbSingleton list of 
  { Nothing  -> LetRec list
  ; Just def -> ifte (isRecursiveDefin (located def)) (LetRec (singleton def)) (Let1 def) }

checkForDuplicates :: List LDefinE -> a -> a
checkForDuplicates defins what = case trieFromListUnique duplicate (map (compose definToPair located) defins) of 
  { Node _ _ -> what } where { duplicate n  = concat [ "multiple declaration of " , quoteString n ] }

-- debug "graph" (trieToList graph) (debug "SCC" sccs (
partitionLets :: List LDefinE -> List Let
partitionLets ldefins = map (compose mkLet (map lkp)) sccs where
  { names = map (compose definedName located) ldefins
  ; isName n = stringElem n names
  ; graph = trieFromList (for ldefins (\ldef -> case ldef of { Located loc def -> case def of { Defin name rhs -> 
      Pair name (filter isName (trieSetToList (exprFreeVars rhs))) }} ))
  ; sccs = dependencyAnalysis (checkForDuplicates ldefins graph)
  ; defTrie = trieFromList (map ldefinToPair ldefins)
  ; lkp n = case trieLookup n defTrie of { Just locy -> case locy of { Located loc y -> Located loc (Defin n y) } 
      ; Nothing -> error "partitionLets: shouldn't happen" } }

-- | Top-level everything is letrec, but we still do the reordering.
reorderProgram :: List (LDefin Expr) -> Program Expr
reorderProgram list = worker (checkRecursiveLets (reorderLets (RecE list MainE))) where
  { worker expr = case expr of
    { LetE defs body -> append (map NonRecursive defs) (worker body)
    ; RecE defs body -> Cons          (Recursive defs) (worker body)
    ; MainE -> Nil }}

-- | check for \"lambdas only\" condition in letrecs
checkRecursiveLets :: Expr -> Expr
checkRecursiveLets expr = go expr where
  { go expr = case expr of
      { VarE _         -> expr
      ; AppE e1 e2     -> AppE (go e1) (go e2)
      ; LamE v body    -> LamE v (go body)
      ; LetE defs body -> LetE (map goDefin defs) (go body)
      ; RecE defs body -> let { bad = filter (\ldef -> not (isLambdaExpr (definedWhat (located ldef)))) defs } 
                          in  case bad of
                                { Nil -> RecE (map goDefin defs) (go body)
                                ; _   -> let { badwhat = map showNameAndLoc bad ; text = intercalate ", " badwhat }
                                in  (error (append "recursive definitions must be lambdas: " text)) }                        
      ; CaseE what brs -> CaseE what (map goBranch brs)
      ; LitE  _        -> expr
      ; ListE list     -> ListE   (map go list)
      ; PrimE p list   -> PrimE p (map go list)
      ; StrE  _        -> expr
      ; MainE          -> expr }
  ; goDefin  ldefin = case ldefin of { Located loc defin -> case defin of 
      { Defin name rhs -> Located loc (Defin name (go rhs)) }}
  ; goBranch branch = case branch of 
      { DefaultE rhs         -> DefaultE (go rhs)
      ; BranchE con args rhs -> BranchE con args (go rhs) } }

reorderLets :: Expr -> Expr
reorderLets expr = go expr where
  { go expr = case expr of
    { VarE  _       -> expr
    ; LitE  _       -> expr
    ; StrE  _       -> expr
    ; AppE  e1 e2   -> AppE (go e1) (go e2)
    ; LamE  n body  -> LamE n (go body)
    ; LetE  defs e  -> LetE (map goDefin defs) (go e)
    ; RecE  defs e  -> let { ps = partitionLets (map goDefin defs) } in letWorker ps (go e)
    ; CaseE e brs   -> CaseE (lfmap go e) (map goBranch brs)
    ; ListE es      -> ListE (map go es)
    ; PrimE p es    -> PrimE p (map go es) 
    ; MainE         -> MainE }
  ; goDefin ldef = lfmap (\def -> case def of { Defin n rhs -> Defin n (go rhs) }) ldef
  ; goBranch branch = case branch of 
      { DefaultE rhs -> DefaultE (go rhs) 
      ; BranchE con args rhs -> BranchE con args (go rhs) }
  ; letWorker ls body = case ls of { Nil -> body ; Cons this rest -> case this of
      { Let1   def1 -> LetE (singleton def1) (letWorker rest body)
      ; LetRec defs -> RecE            defs  (letWorker rest body) }} }

--------------------------------------------------------------------------------
-- * Dependency graphs

type Vtx = Name

type Graph = Trie (List Vtx)

graphToList :: Graph -> List (Pair Vtx Vtx)
graphToList g = concat (map worker (trieToList g)) where
  { worker pair = case pair of { Pair v ws -> map (\w -> Pair v w) ws } }

graphFromList :: List (Pair Vtx Vtx) -> Graph 
graphFromList = trieBuild singleton Cons

-- | NB: if we naively flip by @graphFromList . map swap . graphToList@, we will
-- lose vertices with no inbound edges! So we have to reinsert those 
flipGraph :: Graph -> Graph
flipGraph graph = insertKeys (graphFromList (map swap (graphToList graph))) where
  { keys = trieKeys graph
  ; insertKeys g = foldl (\old k -> trieAlter h k old) g keys
  ; h mb = case mb of { Nothing -> Just Nil ; Just _ -> mb } }

dependencyAnalysis :: Graph -> List (List Vtx)
dependencyAnalysis g = tarjanSCC (flipGraph g)

--------------------------------------------------------------------------------
-- * Tarjan's topologically sorted SCC algorithm

-- | Note: the table @links@ consists of @(index,lowlink)@ pairs
data Tarjan = Tarjan 
  { _next   :: Int
  , _stack  :: List Vtx 
  , _links  :: Trie (Pair Int Int)  
  , _output :: List (List Vtx)
  }
  deriving Show

-- | Based on <https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm>
tarjanSCC :: Graph -> (List (List Vtx))
tarjanSCC graph = case execState (smapM_ worker vtxSet) iniState of { Tarjan _ _ _ out -> out } where
  { iniState = Tarjan 0 [] trieEmpty []
  ; vtxSet   = trieKeys graph
  ; worker v = sbind sget (\state -> case state of { Tarjan next stack links out -> 
      case trieLookup v links of { Nothing -> scc v ; _ -> sreturn Unit }})
  -- scc :: Vtx -> State Tarjan Unit
  ; scc v = sbind sget (\state -> case state of { Tarjan next stack links out -> 
            sseq3 (sput (Tarjan (inc next) (Cons v stack) (trieInsert v (Pair next next) links) out))
                  (successor v) (popAndOut v) })
  -- successor :: Vtx -> State Tarjan Unit
  ; successor v = sforM_ (trieLookupDefault Nil v graph) (\w -> 
      sbind sget (\state -> case state of { Tarjan next stack links output ->
        case trieLookup w links of
          { Nothing -> sseq (scc w) 
              (sbind sget (\state -> case state of { Tarjan next stack links output ->
                case trieLookup v links of { Just vpair -> case vpair of { Pair vi vl -> 
                case trieLookup w links of { Just wpair -> case wpair of { Pair _  wl -> 
                  sput (Tarjan next stack (trieInsert v (Pair vi (min vl wl)) links) output) }}}}}))
          ; Just pair -> case pair of { Pair wi wl -> swhen (stringElem w stack)
               (case trieLookup v links of { Just vpair -> case vpair of { Pair vi vl -> 
                case trieLookup w links of { Just wpair -> case wpair of { Pair wi _  -> 
                  sput (Tarjan next stack (trieInsert v (Pair vi (min vl wi)) links) output) }}}})}  }}))
  -- popAndOut :: Vtx -> State Tarjan Unit
  ; popAndOut v = sbind sget (\state -> case state of { Tarjan next stack links output ->
      case trieLookup v links of { Just vpair -> case vpair of { Pair vi vl -> swhen (eq vi vl) 
        (let { this    =       takeWhile (\x -> not (stringEq x v)) stack 
             ; stack'  = tail (dropWhile (\x -> not (stringEq x v)) stack)
             ; output' = Cons (Cons v this) output }
        in sput (Tarjan next stack' links output') )}}}) }

--------------------------------------------------------------------------------

