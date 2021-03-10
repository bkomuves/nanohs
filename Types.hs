
-- | Common types

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists#-}

module Types where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base

{-% include "Base.hs"  %-}

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

type Program a = List (Defin a)

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

-- | Variables can be a de Bruijn index, or a top-level definition
data Var
  = IdxV Idx
  | TopV Static
  deriving Show

-- | Shift de Bruijn indices in variables
shiftVar :: Int -> Var -> Var
shiftVar ofs var = case var of { IdxV i -> IdxV (plus i ofs) ; _ -> var }

prettyVar :: Var -> String
prettyVar var = case var of 
  { IdxV i -> concat [  "de Bruijn (" , showInt i , ")" ] 
  ; TopV j -> concat [ "static fun (" , showInt j , ")" ] }

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

data Location  = Loc SrcPos SrcPos    deriving Show
data Located a = Located Location a   deriving Show

locStart loc = case loc of { Loc pos1 _ -> pos1 }
locEnd   loc = case loc of { Loc _ pos2 -> pos2 }

location lx = case lx of { Located loc _ -> loc }
located  lx = case lx of { Located _   x -> x   }

locatedStart = compose locStart location
locatedEnd   = compose locEnd   location

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

