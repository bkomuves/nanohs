
-- | Base library

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists#-}

module Base where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------
-- * Prelude
-- ** functions

-- data Unit = Unit deriving Show

id :: a -> a
id = \x -> x

const :: a -> b -> a
const x = \_ -> x

app :: (a -> b) -> a -> b
app f x = f x

compose :: (b -> c) -> (a -> b) -> (a -> c)
compose f g = \x -> f (g x)

compose3 :: (c -> d) -> (b -> c) -> (a -> b) -> (a -> d)
compose3 f g h = \x -> f (g (h x))

flip :: (a -> b -> c) -> (b -> a -> c)
flip f = \x y -> f y x

--------------------------------------------------------------------------------
-- ** numbers

inc :: Int -> Int
inc n = plus n 1

inc2 :: Int -> Int
inc2 n = plus n 2

dec :: Int -> Int
dec n = minus n 1

natRec :: a -> (a -> a) -> Int -> a
natRec z s = go where { go n = ifte (eq n 0) z (s (go (dec n))) }

ceq :: Char -> Char -> Bool
ceq c d = eq (ord c) (ord d)

cneq :: Char -> Char -> Bool
cneq c d = not (ceq c d)

gneq :: Eq a => a -> a -> Bool
gneq x y = not (geq x y)

neq :: Int -> Int -> Bool
neq x y = not (eq x y)

gt :: Int -> Int -> Bool
gt x y = lt y x

ge :: Int -> Int -> Bool
ge x y = le y x

data Ordering = LT | EQ | GT deriving Show

compare :: Int -> Int -> Ordering
compare x y = ifte (lt x y) LT (ifte (eq x y) EQ GT)

-- | the list [0,1,...n-1]
range :: Int -> List Int
range = rangeFrom 0

-- | the list [k,k+1,...k+n-1]
rangeFrom :: Int -> Int -> List Int
rangeFrom k n = ifte (gt n 0) (Cons k (rangeFrom (inc k) (dec n))) Nil

-- -- | the list [-n+1,-n+2,...0] == reverse (map negate (range n))
-- negativeDeBruijnRange :: Int -> List Int
-- negativeDeBruijnRange n = rangeFrom (inc (negate n)) n

--------------------------------------------------------------------------------
-- ** Bool

-- data Bool = True | False deriving Show

-- These are primops for now so they can short-circuit
--
-- and :: Bool -> Bool -> Bool
-- and x ~y = case x of { True -> y ; False -> False }
--
-- or :: Bool -> Bool -> Bool
-- or x ~y = case x of { True -> True ; False -> y }

-- This is a primop only for efficiency reasons
--
-- not :: Bool -> Bool
-- not b = case b of { True -> False ; False -> True }

and3 :: Bool -> Bool -> Bool -> Bool
and3 x y z = and (and x y) z

andList :: List Bool -> Bool
andList list = case list of { Nil -> False ; Cons b bs -> ifte b (andList bs) False }

--------------------------------------------------------------------------------
-- ** Maybe

-- data Maybe a = Nothing | Just a deriving Show

isJust :: Maybe a -> Bool
isJust mb = case mb of { Nothing -> False ; Just _ -> True }

isNothing :: Maybe a -> Bool
isNothing mb = case mb of { Nothing -> True ; Just _ -> False }

fromJust :: Maybe a -> a
fromJust mb = case mb of { Just x -> x ; Nothing -> error "fromJust" }

mbfmap :: (a -> b) -> Maybe a -> Maybe b
mbfmap f mb = case mb of { Just x -> Just (f x) ; Nothing -> Nothing }

catMaybes :: List (Maybe a) -> List a
catMaybes = go where { go list = case list of { Nil -> Nil ; Cons mb rest ->
  case mb of { Nothing -> go rest ; Just x -> Cons x (go rest) } } }

--------------------------------------------------------------------------------
-- ** Either, Pair, Triple

data Either a b = Left a | Right b deriving Show

isLeft :: Either a b -> Bool
isLeft ei = case ei of { Left _ -> True ; Right _ -> False }

isRight :: Either a b -> Bool
isRight ei = case ei of { Left _ -> False ; Right _ -> True }

fromLeft :: Either a b -> a
fromLeft ei = case ei of { Left x -> x ; Right _ -> error "fromLeft" }

fromRight :: Either a b -> b
fromRight ei = case ei of { Right y -> y ; Left _ -> error "fromRight" }

--------------------------------------------------------------------------------
-- ** Pair, Triple

data Pair a b = Pair a b deriving Show

fst :: Pair a b -> a
fst pair = case pair of { Pair x _ -> x }

snd :: Pair a b -> b
snd pair = case pair of { Pair _ y -> y }

swap :: Pair a b -> Pair b a
swap pair = case pair of { Pair x y -> Pair y x }

data Triple a b c = Triple a b c deriving Show

fst3 :: Triple a b c -> a
fst3 triple = case triple of { Triple x _ _ -> x }

snd3 :: Triple a b c -> b
snd3 triple = case triple of { Triple _ y _ -> y }

thd3 :: Triple a b c -> c
thd3 triple = case triple of { Triple _ _ z -> z }

--------------------------------------------------------------------------------
-- ** Lists

-- data List a = Nil | Cons a (List a) deriving (Eq)

singleton :: a -> List a
singleton x = Cons x Nil

head :: List a -> a
head ls = case ls of { Cons x _ -> x ; Nil -> error "head: empty list" }

tail :: List a -> List a
tail ls = case ls of { Nil -> Nil ; Cons _ xs -> xs }

isNil :: List a -> Bool
isNil ls = case ls of { Nil -> True ; Cons _ _ -> False }

mbSingleton :: List a -> Maybe a
mbSingleton list = let { msg = "non-singleton list" } in case list of
  { Cons x xs -> case xs of { Nil -> Just x ; _ -> error msg } ; Nil -> error msg }

mbPair :: List a -> Maybe (Pair a a)
mbPair list = let { msg = "non-two-element list" } in case list of
  { Cons x xs -> case xs of { Cons y ys -> case ys of { Nil -> Just (Pair x y) ; _ -> error msg }
     ; Nil -> error msg } ; Nil -> error msg }

length :: List a -> Int
length ls = case ls of { Nil -> 0 ; Cons _ xs -> inc (length xs) }

index :: Int -> List a -> a
index k ls = case ls of
  { Nil       -> error "index: out of bounds"
  ; Cons x xs -> ifte (eq k 0) x (index (dec k) xs) }

elem :: Eq a => a -> List a -> Bool
elem x = go where { go ls = case ls of { Nil -> False ; Cons y ys -> ifte (geq x y) True (go ys) } }

foldl :: (a -> b -> a) -> (a -> List b -> a)
foldl f x0 list = go x0 list where
  { go x ls = case ls of { Nil -> x ; Cons y ys -> go (f x y) ys }
  }

flipFoldr :: (b -> a -> a) -> (List b -> a -> a)
flipFoldr f list y0 = go list y0 where
  { go ls y = case ls of { Nil -> y ; Cons x xs -> f x (go xs y) }
  }

foldr :: (b -> a -> a) -> (a -> List b -> a)
foldr f x list = flipFoldr f list x

sum :: List Int -> Int
sum = foldl plus 0

reverse :: List a -> List a
reverse = foldl (\xs x -> Cons x xs) Nil

snoc :: List a -> a -> List a
snoc xs y = case xs of { Nil -> singleton y ; Cons z zs -> Cons z (snoc zs y) }

append :: List a -> List a -> List a
append xs ys = case xs of { Nil -> ys ; Cons z zs -> Cons z (append zs ys) }

append3 :: List a -> List a -> List a -> List a
append3 xs ys zs = append xs (append ys zs)

concat :: List (List a) -> List a
concat lls = flipFoldr append lls Nil

map :: (a -> b) -> List a -> List b
map f = go where { go xs = case xs of { Nil -> Nil ; Cons x xs -> Cons (f x) (map f xs) } }

for :: List a -> (a -> b) -> List b
for xs f = map f xs

filter :: (a -> Bool) -> List a -> List a
filter f = go where
  { go list = case list of
     { Nil -> Nil ; Cons x xs -> case f x of
       { False -> go xs ; True -> Cons x (go xs) } } }

replicate :: Int -> a -> List a
replicate n x = go n where { go m = ifte (eq m 0) Nil (Cons x (go (dec m))) }

take :: Int -> List a -> List a
take n ls = case ls of { Nil -> Nil ; Cons x xs -> ifte (eq n 0) Nil (Cons x (take (dec n) xs)) }

drop :: Int -> List a -> List a
drop n ls = case ls of { Nil -> Nil ; Cons x xs -> ifte (eq n 0) ls (drop (dec n) xs) }

takeWhile :: (a -> Bool) -> List a -> List a
takeWhile cond = go where
  { go ls = case ls of { Nil -> Nil ; Cons x xs -> case cond x of
    { True -> Cons x (go xs) ; False -> Nil } } }

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile cond = go where
  { go ls = case ls of { Nil -> Nil ; Cons x xs -> case cond x of
    { True -> go xs ; False -> ls } } }

span :: (a -> Bool) -> List a -> Pair (List a) (List a)
span cond xs = Pair (takeWhile cond xs) (dropWhile cond xs)

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f = go where { go ls1 ls2 = case ls1 of { Nil -> Nil ; Cons x xs -> case ls2 of
  { Nil -> Nil ; Cons y ys -> Cons (f x y) (go xs ys) } } }

zip :: List a -> List b -> List (Pair a b)
zip = zipWith Pair

unzip :: List (Pair a b) -> Pair (List a) (List b)
unzip xys = case xys of { Nil -> Pair Nil Nil ; Cons this rest -> case this of
  { Pair x y -> case unzip rest of { Pair xs ys -> Pair (Cons x xs) (Cons y ys) } } }

-- | Zip with @[0..n-1]@
zipIndex :: List a -> List (Pair Int a)
zipIndex xs = zip (range (length xs)) xs

-- | Zip with @[0..n-1]@
zipWithIndex :: (a -> Int -> b) -> List a -> List b
zipWithIndex f xs = zipWith f xs (range (length xs))

-- | Zip with @replicate n y@
zipConst :: b -> List a -> List (Pair b a)
zipConst y = worker where { worker l = case l of { Nil -> Nil ; Cons x xs -> Cons (Pair y x) (worker xs) }}

-- | Zip with @(first : repeat rest)@
zipFirstRest :: b -> b -> List a -> List (Pair b a)
zipFirstRest first rest xs = case xs of { Nil -> Nil ; Cons x xs -> Cons (Pair first x) (zipConst rest xs) }

--------------------------------------------------------------------------------
-- ** Characters

singleQuoteC    = chr 39
doubleQuoteC    = chr 34
backslashC      = chr 92
newlineC        = chr 10
carriageReturnC = chr 13

isDigit :: Char -> Bool
isDigit ch = and (ge k 48) (le k 57) where { k = ord ch }

mbDigit :: Char -> Maybe Int
mbDigit ch = ifte (isDigit ch) (Just (minus (ord ch) 48)) Nothing

isUpper :: Char -> Bool
isUpper ch = and (ge k 65) (le k 90) where { k = ord ch }

isLower :: Char -> Bool
isLower ch = and (ge k 97) (le k 122) where { k = ord ch }

isAlpha    ch = or (isUpper ch) (isLower ch)
isAlphaNum ch = or (isAlpha ch) (isDigit ch)
isLower_   ch = or (ceq ch '_') (isLower ch)

--------------------------------------------------------------------------------
-- ** Strings

-- type String = List Char

stringEq :: String -> String -> Bool
stringEq = go where { go str1 str2 = case str1 of 
  { Nil       -> case str2 of { Nil -> True  ; _ -> False }
  ; Cons x xs -> case str2 of { Nil -> False ; Cons y ys -> and (ceq x y) (go xs ys) }}}

stringMember :: String -> List String -> Bool
stringMember what ls = case ls of { Nil -> False ; Cons this rest -> case stringEq what this of
  { True -> True ; False -> stringMember what rest }} 

charToString :: Char -> String
charToString x = Cons x Nil

showBool :: Bool -> String
showBool b = case b of { True -> "True" ; False -> "False" }

showChar :: Char -> String
showChar c = Cons singleQuoteC (Cons c (Cons singleQuoteC Nil))

showNat :: Int -> String
showNat n = ifte (lt n 0) (error "showNat: negative") (worker n) where
  { worker n = ifte (eq n 0) "0" (reverse (go n))
  ; go     n = ifte (eq n 0) Nil (Cons (chr (plus (mod n 10) 48)) (go (div n 10)))
  }

showInt :: Int -> String
showInt n = ifte (ge n 0) (showNat n) (Cons '-' (showNat (negate n)))

appendInt :: String -> Int -> String
appendInt s n = append s (showInt n)

readNat :: String -> Maybe Int
readNat str = case str of { Nil -> Nothing ; Cons x xs -> go (reverse str) } where
  { go ds = case ds of { Nil -> Just 0 ; Cons x xs -> case mbDigit x of
    { Just k -> case go xs of { Just n -> Just (plus k (times n 10)) ; Nothing -> Nothing }
    ; Nothing -> Nothing } } }

readInt :: String -> Maybe Int
readInt str = case str of
  { Nil -> Nothing
  ; Cons x xs -> ifte (ceq x '-') (mbfmap negate (readNat xs)) (readNat str) }

quoteChar :: Char -> String
quoteChar x = Cons '`' (Cons x (Cons '`' Nil))

delimString :: Char -> Char -> String -> String
delimString l r xs = Cons l (append xs (Cons r Nil))

backslashEn :: String
backslashEn = [ backslashC  , 'n' ]

doubleQuoteString :: String -> String
doubleQuoteString = delimString doubleQuoteC doubleQuoteC

doubleQuoteStringLn :: String -> String
doubleQuoteStringLn str = delimString doubleQuoteC doubleQuoteC (append str backslashEn)

quoteString :: String -> String
quoteString = delimString '`' '`'

parenString :: String -> String
parenString = delimString '(' ')'

intercalate :: List a -> List (List a) -> List a
intercalate sep = go where
  { go xss = case xss of
    { Nil -> Nil ; Cons ys yss -> case yss of
      { Nil -> ys
      ; _   -> append ys (append sep (go yss)) } } }

unwords :: List String -> String
unwords = intercalate (Cons ' '      Nil)

unlines :: List String -> String
unlines = intercalate (Cons newlineC Nil)

lines :: String -> List String
lines xs = case xs of { Nil -> Nil ; Cons _ _ -> case span (\x -> cneq x newlineC) xs of
  { Pair this rest -> case rest of { Nil -> Cons this Nil ; Cons _ ys -> Cons this (lines ys) } } }

--------------------------------------------------------------------------------
-- ** IO Monad

-- type IO a = (Unit -> a)

ioreturn :: a -> IO a
ioreturn x = (\_ -> x)

ioret_ :: IO Unit
ioret_ = (\_ -> Unit)

-- | Note: we have to be very careful about how to implement bind!
-- (because we are cheating with ML-style IO)
iobind :: IO a -> (a -> IO b) -> IO b
-- iobind action u = case action of { IO f -> IO (\q -> case u (f Unit) of { IO g -> g q } ) }
iobind action u _ = u (action Unit) Unit

ioerror :: String -> IO a
ioerror msg = (\_ -> error msg)

ioliftA2 :: (a -> b -> c) -> IO a -> IO b -> IO c
ioliftA2 f act1 act2 = iobind act1 (\x -> iobind act2 (\y -> ioreturn (f x y)))

ioseq :: IO a -> IO b -> IO b
ioseq f g = iobind f (\_ -> g)

iosequence_ :: List (IO a) -> IO Unit
iosequence_ list = case list of { Nil -> ioret_ ; Cons a as -> ioseq a (iosequence_ as) }

iomapM :: (a -> IO b) -> List a -> IO (List b)
iomapM f list = case list of { Nil -> ioreturn Nil ; Cons x xs -> ioliftA2 Cons (f x) (iomapM f xs) }

ioforM :: List a -> (a -> IO b) -> IO (List b)
ioforM list f = iomapM f list

iomapM_ :: (a -> IO b) -> List a -> IO Unit
iomapM_ f list = case list of { Nil -> ioreturn Unit ; Cons x xs -> ioseq (f x) (iomapM_ f xs) }

ioforM_ :: List a -> (a -> IO b) -> IO Unit
ioforM_ list f = iomapM_ f list

getChar :: IO (Maybe Char)
getChar = (\u -> getChar# u)

putChar :: Char -> IO Unit
putChar c = (\_ -> putChar# c)

exit :: Int -> IO Unit
exit k = (\_ -> exit# k)

print :: Show a => a -> IO Unit
print what = (\_ -> print# what)

getArg :: Int -> IO (Maybe String)
getArg i = (\_ -> getArg# i)

getArgs :: IO (List String)
getArgs = go 0 where { go k = iobind (getArg k) (\mb -> case mb of 
  { Nothing   -> ioreturn Nil 
  ; Just this -> iobind (go (inc k)) (\rest -> ioreturn (Cons this rest)) })}

putStr :: String -> IO Unit
putStr xs = case xs of  { Nil -> ioret_ ; Cons y ys -> ioseq (putChar y) (putStr ys) }

putStrLn :: String -> IO Unit
putStrLn str = ioseq (putStr str) (putChar (chr 10)) 

type FilePath = String

openFile :: FilePath -> IOMode -> IO Handle
openFile fn mode = (\_ -> openFile# fn mode)

hClose :: Handle -> IO Unit
hClose h = (\_ -> hClose# h)

hGetChar :: Handle -> IO (Maybe Char)
hGetChar h = (\_ -> hGetChar# h)

hPutChar :: Handle -> Char -> IO Unit
hPutChar h c = (\_ -> hPutChar# h c)

hGetContents :: Handle -> IO String
hGetContents h = go where { go = iobind (hGetChar h) (\mb -> case mb of 
  { Nothing -> ioreturn Nil 
  ; Just y  -> iobind go (\ys -> ioreturn (Cons y ys)) }) }

hPutStr :: Handle -> String -> IO Unit
hPutStr h = go where { go xs = case xs of { Nil -> ioret_ ; Cons y ys -> ioseq (hPutChar h y) (go ys) } }

hPutStrLn :: Handle -> String -> IO Unit
hPutStrLn h str = ioseq (hPutStr h str) (hPutChar h (chr 10)) 

withFile :: FilePath -> IOMode -> (Handle -> IO a) -> IO a
withFile fn mode action =
  iobind (openFile fn mode) (\handle -> 
  iobind (action handle)    (\result -> 
  iobind (hClose handle)    (\_ -> ioreturn result)))

readFile :: FilePath -> IO String
readFile fn = withFile fn ReadMode hGetContents

writeFile :: FilePath -> String -> IO Unit
writeFile fn text = withFile fn WriteMode (\h -> hPutStr h text)

--------------------------------------------------------------------------------
-- ** State monad

type State s a = s -> Pair s a

runState  :: State s a -> s -> Pair s a
evalState :: State s a -> s -> a
execState :: State s a -> s -> s
runState  f = f
evalState f = compose snd f
execState f = compose fst f

sreturn :: a -> State s a
sreturn x = \s -> Pair s x

sfmap :: (a -> b) -> State s a -> State s b
sfmap f action = \s -> case action s of { Pair s' x -> Pair s' (f x) }

sliftA2 :: (a -> b -> c) -> State s a -> State s b -> State s c
sliftA2 f action1 action2 = \s -> case action1 s of { Pair s' x ->
  case action2 s' of { Pair s'' y -> Pair s'' (f x y) } }

sbind :: State s a -> (a -> State s b) -> State s b
sbind f u = \s -> case f s of { Pair s' x -> u x s' }

sseq :: State s a -> State s b -> State s b
sseq p q = sbind p (\_ -> q)

sseq3 :: State s a -> State s b -> State s c -> State s c
sseq3 p q r = sseq p (sseq q r)

sget :: State s s
sget = \s -> Pair s s

sput :: s -> State s Unit
sput s = \_ -> Pair s Unit

smodify :: (s -> s) -> State s Unit
smodify f = \old -> Pair (f old) Unit

swhen :: Bool -> State s Unit -> State s Unit
swhen b action = ifte b action (sreturn Unit)

ssequence_ :: List (State s a) -> State s Unit
ssequence_ actions = case actions of { Nil -> sreturn Unit ; Cons u us -> sseq u (ssequence_ us) }

smapM :: (a -> State s b) -> List a -> State s (List b)
smapM f list = case list of { Nil -> sreturn Nil ; Cons x xs -> sliftA2 Cons (f x) (smapM f xs) }

sforM :: List a -> (a -> State s b) -> State s (List b)
sforM list f = smapM f list

smapM_ :: (a -> State s b) -> List a -> State s Unit
smapM_ f list = case list of { Nil -> sreturn Unit ; Cons x xs -> sseq (f x) (smapM_ f xs) }

sforM_ :: List a -> (a -> State s b) -> State s Unit
sforM_ list f = smapM_ f list

--------------------------------------------------------------------------------
