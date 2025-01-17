
-- | Primops implemented in Haskell, so the compiler can be hosted by GHC too

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict, StrictData #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module PrimGHC where

import qualified Prelude
import qualified Data.Char
import qualified Data.Bits          as Bits
import qualified System.IO          as IO
import qualified System.IO.Unsafe   as Unsafe
import qualified System.Environment as Env
import qualified System.Exit        as Exit
import qualified Control.Exception  as Exc

import Prelude     ( Int , Char , Eq , Show )
import Data.String ( IsString(..) )
import GHC.Exts    ( IsList  (..) )

--------------------------------------------------------------------------------

import qualified Debug.Trace 

debug :: Show a => List Char -> a -> b -> b 
debug x y z = Debug.Trace.trace msg z where
  msg   = Prelude.concat parts
  parts :: [Prelude.String]
  parts = [ ">>> " , _toGhcString x , " => " , Prelude.show y ]

debug_ :: Show b => List Char -> b -> b 
debug_ x y = debug x y y

--------------------------------------------------------------------------------
-- * Primitive types used by the primops

data Unit = Unit deriving Show

data Bool = False | True deriving Show

data List a = Nil | Cons a (List a) deriving (Eq) 

type String = List Char

data Maybe a = Nothing | Just a deriving Show

type Handle = IO.Handle

data Pair a b = Pair a b deriving Show

--------------------------------------------------------------------------------
-- * IO support

type IO a = IO.IO a

ioreturn :: a -> IO a
ioreturn = Prelude.return

iobind :: IO a -> (a -> IO b) -> IO b
iobind = (Prelude.>>=)

{-# NOINLINE runIO #-}
runIO :: IO a -> IO.IO a
runIO action = do
  Prelude.putStrLn "[rts version = GHC]"
  action

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

bitAnd :: Int -> Int -> Int
bitAnd = (Bits..&.)

bitOr :: Int -> Int -> Int
bitOr = (Bits..|.)

bitXor :: Int -> Int -> Int
bitXor = Bits.xor

shiftL :: Int -> Int -> Int
shiftL = Bits.shiftL

shiftR :: Int -> Int -> Int
shiftR = Bits.shiftR

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

--------------------------------------------------------------------------------

{-# NOINLINE error #-}
error :: String -> a
error msg = Prelude.error (_toGhcString msg)

print :: Show a => a -> IO Unit
print what = (Prelude.>>) (Prelude.print what) (Prelude.return Unit)

--------------------------------------------------------------------------------
-- * IO monad

getChar :: IO (Maybe Char)
getChar = Exc.catch just handler where
  just :: IO.IO (Maybe Char)
  just =  (Prelude.>>=) Prelude.getChar (\c -> Prelude.return (Just c))
  handler :: Exc.IOException -> IO.IO (Maybe Char)
  handler _ = Prelude.return Nothing

putChar :: Char -> IO Unit
putChar c = (Prelude.>>) (Prelude.putChar c) (Prelude.return Unit)

exit :: Int -> IO Unit
exit 0 = Exit.exitWith  Exit.ExitSuccess   
exit k = Exit.exitWith (Exit.ExitFailure k)

getArg :: Int -> IO (Maybe String)
getArg m = Prelude.fmap (index m) (Env.getArgs) where
  index _ [] = Nothing
  index k (this:rest) = case k of 
    0 -> Just (_fromGhcString this) 
    _ -> index ((Prelude.-) k 1) rest 

----------------------------------------

stdin :: Handle
stdin = IO.stdin

stdout :: Handle
stdout = IO.stdout

stderr :: Handle
stderr = IO.stderr

data IOMode
  = ReadMode   
  | WriteMode  
  | AppendMode   
  | ReadWriteMode 
  deriving Show

_toGhcIOMode :: IOMode -> IO.IOMode
_toGhcIOMode mode = case mode of
  ReadMode      -> IO.ReadMode       
  WriteMode     -> IO.WriteMode     
  AppendMode    -> IO.AppendMode    
  ReadWriteMode -> IO.ReadWriteMode 

openFile :: String -> IOMode -> IO Handle
openFile fn mode = IO.openFile (_toGhcString fn) (_toGhcIOMode mode)

hClose :: Handle -> IO Unit
hClose h = (Prelude.>>) (IO.hClose h) (Prelude.return Unit) 

hGetChar :: Handle -> IO (Maybe Char)
hGetChar h = Exc.catch just handler where
  just :: IO.IO (Maybe Char)
  just =  (Prelude.>>=) (IO.hGetChar h) (\c -> Prelude.return (Just c))
  handler :: Exc.IOException -> IO.IO (Maybe Char)
  handler _ = Prelude.return Nothing

hPutChar :: Handle -> Char -> IO Unit
hPutChar h c = (Prelude.>>) (IO.hPutChar h c) (Prelude.return Unit) 

hPutStr :: Handle -> String -> IO Unit
hPutStr h s = (Prelude.>>) (IO.hPutStr h (_toGhcString s)) (Prelude.return Unit) 

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

show :: Show a => a -> String
show x = _fromGhcString (Prelude.show x)

instance Show a => Show (List a) where show list = Prelude.show (_toGhcList list)

instance IsString (List Char) where fromString = _fromGhcString

instance IsList (List a) where
  type (Item (List a)) = a
  fromList = _fromGhcList
  toList   = _toGhcList

--------------------------------------------------------------------------------
