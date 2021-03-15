
-- | Common types and functions

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Types where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Containers

{-% include "Base.hs"        %-}
{-% include "Containers.hs"  %-}

--------------------------------------------------------------------------------
-- * Some common types

-- | Names
type Name = String

-- | Arity
type Arity = Int

-- | De Bruijn level
type Level = Int

-- | De Bruijn index
type Idx = Int

-- | Constructor index
type Con = Int

-- | Static function index
type Static = Int

-- | Mapping constructor names to constructor tags
type DataConTable = Trie Con

--------------------------------------------------------------------------------
-- ** Named things

-- | We want to keep names for debugging \/ pretty printing
data Named a = Named Name a deriving Show

nfmap :: (a -> b) -> Named a -> Named b
nfmap f named = case named of { Named name x -> Named name (f x) }

forgetName :: Named a -> a
forgetName x = case x of { Named _ y -> y }

nameOf :: Named a -> String
nameOf x = case x of { Named n _ -> n }

--------------------------------------------------------------------------------
-- ** Definitions

-- | Definitions
data Defin a = Defin Name a deriving Show

fmapDefin :: (a -> b) -> Defin a -> Defin b
fmapDefin f defin = case defin of { Defin n x -> Defin n (f x) }

definedName :: Defin a -> Name
definedName defin = case defin of { Defin n _ -> n }

definedWhat :: Defin a -> a
definedWhat defin = case defin of { Defin _ e -> e }

definToPair :: Defin a -> Pair Name a
definToPair def = case def of { Defin n rhs -> Pair n rhs }

type Program a = List (Defin a)

--------------------------------------------------------------------------------
-- ** Literals

data Literal
  = IntL Int
  | ChrL Char
  | StrL String
  deriving (Eq,Show)

showLiteral :: Literal -> String
showLiteral lit = case lit of
  { IntL n -> showInt  n
  ; ChrL c -> showChar c
  ; StrL s -> doubleQuoteString s }

--------------------------------------------------------------------------------
-- ** Variables

-- | Variables can be a de Bruijn index, or a top-level definition, or a static string index
data Var
  = IdxV Idx
  | TopV Static
  | StrV Int
  deriving Show

-- | Shift de Bruijn indices in variables
shiftVar :: Int -> Var -> Var
shiftVar ofs var = case var of { IdxV i -> IdxV (plus i ofs) ; _ -> var }

prettyVar :: Var -> String
prettyVar var = case var of 
  { IdxV i -> concat [  "de_Bruijn(" , showInt i , ")" ] 
  ; TopV j -> concat [ "static_fun(" , showInt j , ")" ] 
  ; StrV k -> concat [ "static_str(" , showInt k , ")" ]}

--------------------------------------------------------------------------------
-- ** Atoms

-- | Things which can be applied, case-branched, passed to primops
data Atom
  = VarA (Named Var)
  | ConA (Named Con)
  | KstA Literal
  deriving Show

-- | Shift de Bruijn indices in atoms
shiftAtom :: Int -> Atom -> Atom
shiftAtom ofs atom = case atom of  { VarA namedVar -> VarA (nfmap (shiftVar ofs) namedVar) ; _ -> atom }

prettyAtom :: Atom -> String
prettyAtom atom = case atom of
  { VarA var  -> prettyVar (forgetName var)
  ; ConA ncon -> nameOf ncon
  ; KstA lit  -> showLiteral lit }

--------------------------------------------------------------------------------
-- ** Source positions and locations

-- | @SrcPos row col@; starting from (1,1)
data SrcPos = SrcPos Int Int deriving Show

startSrcPos :: SrcPos
startSrcPos = SrcPos 1 1

startCol :: SrcPos -> SrcPos
startCol pos = case pos of { SrcPos row col -> SrcPos row 1 }

nextCol :: SrcPos -> SrcPos
nextCol pos = case pos of { SrcPos row col -> SrcPos row (inc col) }

nextRow :: SrcPos -> SrcPos
nextRow pos = case pos of { SrcPos row col -> SrcPos (inc row) 1 }

nextSrcPos :: Char -> SrcPos -> SrcPos
nextSrcPos ch pos
  = ifte (ceq ch newlineC       ) (nextRow  pos)
  ( ifte (ceq ch carriageReturnC) (startCol pos) (nextCol pos) )

showSrcPos :: SrcPos -> String
showSrcPos pos = case pos of { SrcPos row col ->
  append ("line ") (append3 (showNat row) (", column ") (showNat col)) }

showSrcPos_ :: SrcPos -> String
showSrcPos_ pos = case pos of { SrcPos row col -> (append3 (showNat row) ":" (showNat col)) }

showSrcPos' :: FilePath -> SrcPos -> String
showSrcPos' fname pos = append3 "file " (doubleQuoteString fname) (append ", " (showSrcPos pos))

showLocation :: Location -> String
showLocation loc = case loc of { Loc fname pos1 pos2 -> concat
  [ "file " , doubleQuoteString fname , ", " , showSrcPos_ pos1 , "--" , showSrcPos_ pos2 ] }

data Location  = Loc FilePath SrcPos SrcPos deriving Show
data Located a = Located Location a         deriving Show

type LName = Located Name

locFn    loc = case loc of { Loc fn _ _    -> fn   }
locStart loc = case loc of { Loc _  pos1 _ -> pos1 }
locEnd   loc = case loc of { Loc _  _ pos2 -> pos2 }

location lx = case lx of { Located loc _ -> loc }
located  lx = case lx of { Located _   x -> x   }

locatedStart = compose locStart location
locatedEnd   = compose locEnd   location

fakeLocation  = Loc "<source>" (SrcPos 0 0) (SrcPos 0 0)
fakeLocated x = Located fakeLocation x

--------------------------------------------------------------------------------
-- ** Tokens

data Special
  = LParen | RParen | LBrace | RBrace | LBracket | RBracket | Dot
  | Comma | Semicolon | EqualSign | Lambda | Pipe | Arrow | DArrow | HasType
  deriving (Eq,Show)

data Token
  = VarTok   Name
  | LitTok   Literal
  | SpecTok  Special
  | WhiteTok
  deriving (Eq,Show)

-- | Token wiht a location
type LToken = Located Token

--------------------------------------------------------------------------------
-- * matching on short lists

unary   :: List a -> (a -> b)           -> b
binary  :: List a -> (a -> a -> b)      -> b
ternary :: List a -> (a -> a -> a -> b) -> b
unary   args f = case args of { Cons x xs -> f x             ; Nil -> error "unary: not enough arguments"   }
binary  args f = case args of { Cons x xs -> unary  xs (f x) ; Nil -> error "binary: not enough arguments"  }
ternary args f = case args of { Cons x xs -> binary xs (f x) ; Nil -> error "ternary: not enough arguments" }

--------------------------------------------------------------------------------
