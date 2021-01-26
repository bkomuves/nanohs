
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module PrimGHC where

import qualified Prelude
import qualified Control.Monad
import qualified Data.Char
import qualified System.IO.Unsafe as Unsafe
import Prelude ( Int , Char , Eq , Show )
import Data.String ( IsString(..) )
import GHC.Exts    ( IsList  (..) )

--------------------------------------------------------------------------------
-- * Primitive types used by the primops

data Unit = Unit deriving Show

data Bool = False | True deriving Show

data List a = Nil | Cons a (List a) deriving (Eq) 

type String = List Char

--------------------------------------------------------------------------------
-- * Built-ins \/ primops

negate :: Int -> Int
negate = Prelude.negate

plus :: Int -> Int -> Int
plus = (Prelude.+)

minus :: Int -> Int -> Int
minus = (Prelude.-)

times :: Int -> Int -> Int
times = (Prelude.*)

div :: Int -> Int -> Int
div = Prelude.div

mod :: Int -> Int -> Int
mod = Prelude.mod

chr :: Int -> Char
chr = Data.Char.chr

ord :: Char -> Int
ord = Data.Char.ord

-- | If-then-else *must* be lazy. Hence for now it is a primop
ifte :: Bool -> a -> a -> a
ifte b ~x ~y = case b of { True -> x ; False -> y }

-- | It is useful if @and@ \/ @or@ shortcircuits, hence they are primops
and :: Bool -> Bool -> Bool
and x ~y = case x of { True -> y ; False -> False }

or :: Bool -> Bool -> Bool
or x ~y = case x of { True -> True ; False -> y }

-- | @not@ could be user-defined, but @and@, @or@ are already primops, and it's faster this way
not :: Bool -> Bool
not x = case x of { True -> False ; False -> True }

geq :: Eq a => a -> a -> Bool
geq x y = _fromGhcBool ((Prelude.==) x y)

eq :: Int -> Int -> Bool
eq x y = _fromGhcBool ((Prelude.==) x y)

lt :: Int -> Int -> Bool
lt x y = _fromGhcBool ((Prelude.<)  x y)

le :: Int -> Int -> Bool
le x y = _fromGhcBool ((Prelude.<=) x y)

error :: String -> a
error msg = Prelude.error (_toGhcString msg)

{-# NOINLINE getChar #-}
getChar :: Unit -> Char
getChar = \_ -> Unsafe.unsafePerformIO (Prelude.getChar)

{-# NOINLINE putChar #-}
putChar :: Char -> Unit
putChar ch = Unsafe.unsafePerformIO ( (Prelude.>>) (Prelude.putChar ch) (Prelude.return Unit) )

--------------------------------------------------------------------------------
-- * Marshalling to\/from standard Haskell types

_fromGhcBool :: Prelude.Bool -> Bool
_fromGhcBool b = case b of { Prelude.True -> True ; Prelude.False -> False }

_fromGhcList :: [a] -> List a
_fromGhcList = go where { go [] = Nil ; go (x:xs) = Cons x (go xs) }

_toGhcList :: List a -> [a]
_toGhcList = go where { go Nil = [] ; go (Cons x xs) =  x : (go xs) }

_fromGhcString :: Prelude.String -> String
_fromGhcString = _fromGhcList

_toGhcString :: String -> Prelude.String
_toGhcString = _toGhcList

instance Show a => Show (List a) where show list = Prelude.show (_toGhcList list)

instance IsString (List Char) where fromString = _fromGhcString

instance IsList (List a) where
  type (Item (List a)) = a
  fromList = _fromGhcList
  toList   = _toGhcList

--------------------------------------------------------------------------------
