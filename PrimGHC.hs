
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

import qualified Debug.Trace 
debug :: Show a => List Char -> a -> b -> b 
debug x y z = Debug.Trace.trace msg z where
  msg   = Prelude.concat parts
  parts :: [Prelude.String]
  parts = [ ">>> " , _toGhcString x , " => " , Prelude.show y ]

--------------------------------------------------------------------------------
-- * Primitive types used by the primops

data Unit = Unit deriving Show

data Bool = False | True deriving Show

data List a = Nil | Cons a (List a) deriving (Eq) 

type String = List Char

data Maybe a = Nothing | Just a deriving Show

type Handle = IO.Handle

type IO a = (Unit -> a)

runIO# :: IO a -> IO.IO a
runIO# (f) = do
  Prelude.putStrLn "[rts version : GHC]"
  case f Unit of { y -> Prelude.return y }

-- _GhcUnit :: ()
-- _GhcUnit = ()

-- _GhcReturnUnit :: Prelude.IO ()
-- _GhcReturnUnit = Prelude.return ()

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

{-# NOINLINE error #-}
error :: String -> a
error msg = Prelude.error (_toGhcString msg)

{-# NOINLINE print# #-}
print# :: Show a => a -> Unit
print# what = Unsafe.unsafePerformIO ((Prelude.>>) (Prelude.print what) (Prelude.return Unit))

--------------------------------------------------------------------------------
-- * ML-style IO (we use the hash to distinguish from the IO monad)

{-# NOINLINE getChar# #-}
getChar# :: Unit -> Maybe Char
getChar# _ = Unsafe.unsafePerformIO (Exc.catch just handler) where
  just :: IO.IO (Maybe Char)
  just =  (Prelude.>>=) Prelude.getChar (\c -> Prelude.return (Just c))
  handler :: Exc.IOException -> IO.IO (Maybe Char)
  handler _ = Prelude.return Nothing

{-# NOINLINE putChar# #-}
putChar# :: Char -> Unit
putChar# c = Unsafe.unsafePerformIO ( (Prelude.>>) (Prelude.putChar c) (Prelude.return Unit) )

{-# NOINLINE exit# #-}
exit# :: Int -> Unit
exit# 0 = Unsafe.unsafePerformIO (Exit.exitWith  Exit.ExitSuccess   )
exit# k = Unsafe.unsafePerformIO (Exit.exitWith (Exit.ExitFailure k))

{-# NOINLINE getArg# #-}
getArg# :: Int -> Maybe String
getArg# m = index m (Unsafe.unsafePerformIO Env.getArgs) where
  index _ [] = Nothing
  index k (this:rest) = case k of { 0 -> Just (_fromGhcString this) ; _ -> index ((Prelude.-) k 1) rest } 

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

{-# NOINLINE openFile# #-}
openFile# :: String -> IOMode -> Handle
openFile# fn mode = Unsafe.unsafePerformIO (IO.openFile (_toGhcString fn) (_toGhcIOMode mode))

{-# NOINLINE hClose# #-}
hClose# :: Handle -> Unit
hClose# h = Unsafe.unsafePerformIO ( (Prelude.>>) (IO.hClose h) (Prelude.return Unit) ) 

{-# NOINLINE hGetChar# #-}
hGetChar# :: Handle -> Maybe Char
hGetChar# h = Unsafe.unsafePerformIO (Exc.catch just handler) where
  just :: IO.IO (Maybe Char)
  just =  (Prelude.>>=) (IO.hGetChar h) (\c -> Prelude.return (Just c))
  handler :: Exc.IOException -> IO.IO (Maybe Char)
  handler _ = Prelude.return Nothing

{-# NOINLINE hPutChar# #-}
hPutChar# :: Handle -> Char -> Unit
hPutChar# h c = Unsafe.unsafePerformIO ( (Prelude.>>) (IO.hPutChar h c) (Prelude.return Unit) )

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
