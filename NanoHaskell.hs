
-- | The idea is to write a self-hosting compiler (and interpreter) in
-- a very small subset of Haskell (basically untyped lambda calculus +
-- constructors); but with Haskell-compatible syntax, so that the same
-- program can be also executed by GHC.
--
-- * no static type system (untyped lambda calculus)
-- * na data type declarations (constructors are arbitrary capitalized names)
-- * no modules; single-file (TODO: allow imports)
-- * strict language (if-then-else must be lazy though; "and" + "or" shortcuts too)
-- * only simple pattern matching + default branch (TODO: nested patterns)
-- * no infix operators
-- * list construction syntax @[a,b,c]@ is supported
-- * no indentation syntax (only curly braces), except for top-level blocks
-- * only line comments, starting at the beginning of the line
-- * built-in data types: Int, Char, Bool, List, Maybe + primops
-- * universal polymorphic equality comparison primop?
-- * no escaping in character \/ string constants
-- * minimal IO: at the moment standard input \/ output only, command line
--   arguments, (fatal) errors, early exit
--
-- We can make the same source file to be accepted by both GHC and
-- itself by recognizing and ignoring GHC-specific lines (pragmas, imports,
-- type signatures, datatype declarations, type synonyms). We just put
-- primops implementations into a PrimGHC module (as imports are ignored).
--
-- We can have several backends:
--
-- * C99 on 64 bit architectures
-- * x86-64 assembly
-- * some simple bytecode virtual machine
--
-- For bootstrapping purposes it seems to be useful to have a very simple virtual 
-- machine, for which an interpreter can be very easily written in C or any other 
-- language.
--

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists#-}

module NanoHaskell where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------
-- * Config

-- targetOS :: Target
-- targetOS = MacOS

--------------------------------------------------------------------------------
-- * entry point (required below)

-- main :: Unit
-- main = error "nanoMain"
main = (showInt (sum (range 11)))

-- main = Pair
--   (sum (rangeFrom 1 10))
--   (showInt (sum (range 101)))

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

-- | the list [-n+1,-n+2,...0] == reverse (map negate (range n))
negativeDeBruijnRange :: Int -> List Int
negativeDeBruijnRange n = rangeFrom (inc (negate n)) n

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
    { True -> go xs ; False -> xs } } }

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
-- ** Sets

-- | We model sets as sorted lists. We would need an Ord instance so we only
-- do it for Int-s.
type IntSet = List Int

setEmpty :: IntSet
setEmpty = Nil

setMember :: Int -> IntSet -> Bool
setMember = elem

setSingleton :: Int -> IntSet
setSingleton x = Cons x Nil

setInsert :: Int -> IntSet -> IntSet
setInsert k = go where
  { go set = case set of { Nil -> Cons k Nil ; Cons x xs -> case compare k x of
    { LT -> Cons k set ; EQ -> set ; GT -> Cons x (go xs) } } }

setDelete :: Int -> IntSet -> IntSet
setDelete k = go where
  { go set = case set of { Nil -> Nil ; Cons x xs -> case compare k x of
    { LT -> set ; EQ -> xs ; GT -> Cons x (go xs) } } }

setUnion :: IntSet -> IntSet -> IntSet
setUnion set1 set2 = flipFoldr setInsert set1 set2

setUnions :: List IntSet -> IntSet
setUnions = foldl setUnion setEmpty

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

isLower_ ch = or (ceq ch '_') (isLower ch)

--------------------------------------------------------------------------------
-- ** Strings

-- type String = List Char

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
-- ** Association maps (sorted lists of (key,value) pairs)

type Map k v = List (Pair k v)

mapEmpty :: Map k v
mapEmpty = Nil

mapSingleton :: k -> v -> Map k v
mapSingleton k v = Cons (Pair k v) Nil

-- | This can be used for sorting. Of course it's quadratic...
mapFromList :: List (Pair Int v) -> Map Int v
mapFromList list = foldl g mapEmpty list where 
  { g old pair = case pair of { Pair k v -> mapInsert k v (const v) old } }

-- mapLookup :: Eq k => k -> Map k v -> Maybe v
mapLookup :: Int -> Map Int v -> Maybe v
mapLookup key list = go list where
  { go ls = case ls of
    { Nil -> Nothing ; Cons this rest -> case this of
      { Pair k v -> ifte (eq k key) (Just v) (go rest) } } }

-- mapDelete :: Eq k => k -> Map k v -> Map k v
mapDelete :: Int -> Map Int v -> Map Int v
mapDelete key = go where
  { go kvs = case kvs of { Nil -> Nil ; Cons kv rest -> case kv of
    { Pair k v -> ifte (eq k key) rest (Cons kv (go rest)) } } }

-- | For proper insertion we need ordering, but we only have that for Ints...
mapInsert :: Int -> v -> (v -> v) -> Map Int v -> Map Int v
mapInsert key y f = go where
  { go kvs = case kvs of { Nil -> Cons (Pair key y) Nil ; Cons kv rest -> case kv of
    { Pair k v -> case compare k key of
      { LT -> Cons kv               (go rest)
      ; EQ -> Cons (Pair k   (f v))     rest
      ; GT -> Cons (Pair key y    )     kvs } } } }

mapAdjust :: Int -> (v -> v) -> Map Int v -> Map Int v
mapAdjust key f = go where
  { go kvs = case kvs of { Nil -> Nil ; Cons kv rest -> case kv of
    { Pair k v -> case compare k key of
      { LT -> Cons kv               (go rest)
      ; EQ -> Cons (Pair k   (f v))     rest
      ; GT -> kvs } } } }

--------------------------------------------------------------------------------
-- ** Trie

data Trie a = Node (Maybe a) (Map Int (Trie a)) deriving Show

trieEmpty :: Trie a
trieEmpty = Node Nothing Nil

trieSingleton :: String -> a -> Trie a
trieSingleton str y = case str of { Nil -> Node (Just y) mapEmpty
  ; Cons x xs -> Node Nothing (mapSingleton (ord x) (trieSingleton xs y)) }

trieLookup :: String -> Trie a -> Maybe a
trieLookup str trie = case trie of { Node mb table -> case str of { Nil -> mb
  ; Cons x xs -> case mapLookup (ord x) table of { Nothing -> Nothing
    ; Just trie' -> trieLookup xs trie' } } }

trieInsert :: String -> a -> Trie a -> Trie a
trieInsert string y = go string where
  { go str trie = case trie of { Node mb table -> case str of
    { Nil -> Node (Just y) table
    ; Cons x xs -> Node mb (mapInsert (ord x) (trieSingleton xs y) (go xs) table) } } }

trieDelete :: String -> Trie a -> Trie a
trieDelete str trie = case trie of { Node mb table -> case str of
  { Nil -> Node Nothing table
  ; Cons x xs -> Node mb (mapAdjust (ord x) (trieDelete xs) table) } }

trieFromList :: List (Pair String a) -> Trie a
trieFromList = foldr f trieEmpty where { f kv trie = case kv of { Pair k v -> trieInsert k v trie } }

trieToList :: Trie a -> List (Pair String a)
trieToList = go where { go trie = case trie of { Node mb table -> let
  { f pair = case pair of { Pair k trie' -> map (prepend (chr k)) (go trie') }
  ; rest = concat (map f table)
  ; prepend x pair = case pair of { Pair xs y -> Pair (Cons x xs) y } }
  in case mb of { Nothing -> rest ; Just y -> Cons (Pair Nil y) rest } } }

--------------------------------------------------------------------------------
-- ** IO Monad

type IO a = Unit -> a

runIO :: IO a -> a
runIO action = action Unit

ioreturn :: a -> IO a
ioreturn x = \_ -> x

ioret_ :: IO Unit
ioret_ = \_ -> Unit

-- | Note: we have to be very careful about how to implement bind!
-- (because we are cheating with ML-style IO)
iobind :: IO a -> (a -> IO b) -> IO b
iobind action u _ = u (action Unit) Unit

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
getChar = getChar#

putChar :: Char -> IO Unit
putChar c = \_ -> putChar# c

exit :: Int -> IO Unit
exit k = \_ -> exit# k

getArg :: Int -> IO (Maybe String)
getArg i = \_ -> getArg# i 

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
openFile fn mode = \_ -> openFile# fn mode

hClose :: Handle -> IO Unit
hClose h = \_ -> hClose# h

hGetChar :: Handle -> IO (Maybe Char)
hGetChar h = \_ -> hGetChar# h

hPutChar :: Handle -> Char -> IO Unit
hPutChar h c = \_ -> hPutChar# h c

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
-- * Parsing
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

locatedL :: Parser tok a -> Parser tok (Located a)
locatedL parser = pbind getSrcPos (\pos1 ->
                  pbind parser    (\what ->
                  pbind getSrcPos (\pos2 -> preturn (Located (Loc pos1 pos2) what))))

type LList a = List (Located a)
type LString = LList Char

addLocations :: String -> LString
addLocations = go startSrcPos where { go pos str = case str of { Nil -> Nil
  ; Cons x xs -> let { pos' = nextSrcPos x pos } in Cons (Located (Loc pos pos') x) (go pos' xs) } }

--------------------------------------------------------------------------------
-- ** Parser combinators

data ParseResult tok a
  = ParseOk a SrcPos (LList tok)
  | ParseErr  SrcPos
  deriving Show

type Parser tok a = SrcPos -> LList tok -> ParseResult tok a

runParser' :: Parser tok a -> LList tok -> ParseResult tok a
runParser' parser input = case input of { Nil -> error "empty input"
  ; Cons locx _ -> parser (locatedStart locx) input }

runParser :: Parser tok a -> LList tok -> Either String a
runParser p input = case runParser' p input of
  { ParseOk x pos rest -> case rest of
    { Nil -> Right x
    ; Cons _ _ -> Left (append "unexpected extra token at " (showSrcPos pos)) }
  ; ParseErr pos -> Left (append "parse error at " (showSrcPos pos)) }

runParser_ :: Parser tok a -> LList tok -> a
runParser_ p input = case runParser p input of { Right y -> y ; Left msg -> error msg }

preturn :: a -> Parser tok a
preturn x pos str = ParseOk x pos str

pfail :: Parser tok a
pfail pos str = ParseErr pos

pfmap :: (a -> b) -> Parser tok a -> Parser tok b
pfmap f p = \pos str -> case p pos str of
  { ParseOk x pos' str' -> ParseOk (f x) pos' str'
  ; ParseErr  pos'      -> ParseErr pos' }

preplace :: b -> Parser tok a -> Parser tok b
preplace x = pfmap (const x)

pbind :: Parser tok a -> (a -> Parser tok b) -> Parser tok b
pbind p u = \pos str -> case p pos str of
  { ParseOk x pos' str' -> u x pos' str'
  ; ParseErr  pos'      -> ParseErr pos' }

pseq  :: Parser tok a -> Parser tok b -> Parser tok b
pseq  p q = pbind p (\_ -> q)

ppost :: Parser tok a -> Parser tok b -> Parser tok a
ppost p q = pbind p (\x -> pbind q (\_ -> preturn x))

getSrcPos :: Parser tok SrcPos
getSrcPos = \pos str -> ParseOk pos pos str

alternative :: Parser tok a -> Parser tok a -> Parser tok a
alternative p q = \pos str -> case p pos str of
  { ParseOk x pos' str' -> ParseOk x pos' str'
  ; ParseErr _          -> q pos str }

choice :: List (Parser tok a) -> Parser tok a
choice list = case list of { Nil -> pfail ; Cons p ps -> alternative p (choice ps) }

optional :: Parser tok a -> Parser tok (Maybe a)
optional p = \pos str -> case p pos str of
  { ParseOk x pos' str' -> ParseOk (Just x) pos' str'
  ; ParseErr  _pos'     -> ParseOk Nothing  pos  str  }

option :: a -> Parser tok a -> Parser tok a
option x0 p = \pos str -> case p pos str of
  { ParseOk x pos' str'  -> ParseOk x  pos' str'
  ; ParseErr  _pos'      -> ParseOk x0 pos  str  }

many :: Parser tok a -> Parser tok (List a)
many p = pbind (optional p) (\mb -> case mb of
  { Nothing -> preturn Nil ; Just x -> pbind (many p) (\xs -> preturn (Cons x xs)) })

many1 :: Parser tok a -> Parser tok (List a)
many1 p = pbind p        (\x ->
          pbind (many p) (\xs -> preturn (Cons x xs)))

manyTill :: Parser tok end -> Parser tok a -> Parser tok (List a)
manyTill end p = go where { go = alternative (preplace Nil end)
  (pbind p (\x -> pbind go (\xs -> preturn (Cons x xs)))) }

sepEndBy :: Parser tok sep -> Parser tok end -> Parser tok a -> Parser tok (List a)
sepEndBy sep end p = alternative (preplace Nil end) (sepEndBy1 sep end p)

sepEndBy1 :: Parser tok sep -> Parser tok end -> Parser tok a -> Parser tok (List a)
sepEndBy1 sep end p = pbind p (\x -> alternative
  (preplace (Cons x Nil) end)
  (pseq sep (pbind (sepEndBy sep end p) (\xs -> preturn (Cons x xs)))))

accept :: (tok -> Maybe a) -> Parser tok a
accept f pos toks = case toks of
  { Nil -> ParseErr pos
  ; Cons locx xs -> case locx of { Located loc x -> case f x of
    { Just y    -> ParseOk y (locEnd loc) xs
    ; Nothing   -> ParseErr pos } } }

satisfy :: (tok -> Bool) -> Parser tok tok
satisfy f pos toks = case toks of
  { Nil -> ParseErr pos
  ; Cons locx xs -> case locx of { Located loc x -> case f x of
    { True  -> ParseOk x (locEnd loc) xs
    ; False -> ParseErr pos } } }

anyToken :: Parser tok tok
anyToken = satisfy (\_ -> True)

token :: Eq tok => tok -> Parser tok tok
token t = satisfy (geq t)

tokens :: Eq tok => List tok -> Parser tok (List tok)
tokens toks = case toks of { Nil -> preturn Nil ; Cons t ts ->
  pbind (token t) (\x -> pbind (tokens ts) (\xs -> preturn (Cons x xs))) }

oneOf :: Eq tok => List tok -> Parser tok tok
oneOf list = satisfy (\x -> elem x list)

noneOf :: Eq tok => List tok -> Parser tok tok
noneOf list = satisfy (\x -> not (elem x list))

eof :: Parser tok Unit
eof pos str = case str of { Nil -> ParseOk Unit pos str ; Cons _ _ -> ParseErr pos }

--------------------------------------------------------------------------------
-- * Parsing the pseudo-Haskell syntax
-- ** Lexer

type Lexer a = Parser Char a

digitL    = satisfy isDigit
lowerL    = satisfy isLower
upperL    = satisfy isUpper
alphaL    = satisfy isAlpha
_alphaL   = satisfy (\ch -> or (ceq ch '_') (isAlpha ch))
alphaNumL = satisfy isAlphaNum

spaces0 :: Lexer Int
spaces0 = pfmap length (many (token ' '))

spaces1 :: Lexer Int
spaces1 = pfmap length (many1 (token ' '))

digitsL :: Lexer String
digitsL = many1 digitL

natL :: Lexer Int
natL = pbind digitsL (\xs -> case readNat xs of { Just n -> preturn n ; Nothing -> pfail })

intL :: Lexer Int
intL = pbind (optional (token '-'))
  (\mb -> case mb of { Nothing -> natL ; Just _ -> pfmap negate natL })

charLiteralL :: Lexer Char
charLiteralL =
  pbind (token singleQuoteC) (\_ ->
  pbind (anyToken          ) (\c ->
  pbind (token singleQuoteC) (\_ -> preturn c)))

stringLiteralL :: Lexer String
stringLiteralL =
  pbind (token doubleQuoteC)                 (\_  ->
  pbind (many (satisfy (cneq doubleQuoteC))) (\xs ->
  pbind (token doubleQuoteC)                 (\_  -> preturn xs)))

identifierL :: Lexer Name
identifierL = pbind _alphaL                                      (\x  ->
              pbind (many (alternative alphaNumL (oneOf "_'#"))) (\xs ->
              preturn (Cons x xs)))

data Literal
  = IntL Int
  | ChrL Char
  | StrL String
  deriving (Eq,Show)

literalL :: Lexer Literal
literalL = choice
  [ pfmap IntL intL
  , pfmap ChrL charLiteralL
  , pfmap StrL stringLiteralL ]

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

type LToken = Located Token

mbVar  :: Token -> Maybe Name
mbLit  :: Token -> Maybe Literal
mbSpec :: Token -> Maybe Special

mbVar  tok = case tok of { VarTok  v -> Just v ; _ -> Nothing }
mbLit  tok = case tok of { LitTok  l -> Just l ; _ -> Nothing }
mbSpec tok = case tok of { SpecTok s -> Just s ; _ -> Nothing }

mbVarL :: Token -> Maybe Name
mbVarU :: Token -> Maybe Name
mbVarL tok = case mbVar tok of { Just str -> ifte (isLower_ (head str)) (Just str) Nothing }  
mbVarU tok = case mbVar tok of { Just str -> ifte (isUpper  (head str)) (Just str) Nothing }  

mbStrLit  :: Token -> Maybe String
mbStrLit tok = case mbLit tok of { Nothing -> Nothing ; Just lit -> 
  case lit of { StrL s -> Just s ; _ -> Nothing } }

isNotWhite :: Token -> Bool
isNotWhite tok = case tok of { WhiteTok -> False ; _ -> True }

specialL :: Lexer Special
specialL = choice
  [ preplace LParen    (token  '(' )
  , preplace RParen    (token  ')' )
  , preplace LBrace    (token  '{' )
  , preplace RBrace    (token  '}' )
  , preplace LBracket  (token  '[' )
  , preplace RBracket  (token  ']' )
  , preplace Arrow     (tokens "->")
  , preplace DArrow    (tokens "=>")
  , preplace HasType   (tokens "::")
  , preplace Comma     (token  ',' )
  , preplace Semicolon (token  ';' )
  , preplace EqualSign (token  '=' )
  , preplace Pipe      (token  '|' )
  , preplace Lambda    (token  backslashC)
  , preplace Dot       (token  '.' )
  ]

lexemeL :: Lexer Token
lexemeL = choice
  [ pfmap    LitTok   literalL
  , pfmap    SpecTok  specialL
  , pfmap    VarTok   identifierL
  , preplace WhiteTok spaces1
  ]

-- | 0x0A, or 0x0D, or 0x0D,0x0A.
eol_ :: Lexer Unit
eol_ = alternative linux windows where
  { linux   = preplace Unit (token newlineC)
  ; windows = preplace Unit (pseq (token carriageReturnC) (optional (token newlineC))) }

eol :: Lexer Unit
eol = alternative eol_ eof

eolIndent :: Lexer Int
eolIndent = alternative (pseq eol_ spaces0) (preplace 0 eof)

commentL :: Lexer String
commentL = choice [ comment1 , comment2 ] where
  { comment1 = pseq (tokens "--" ) (ppost (many (noneOf [newlineC,carriageReturnC])) eol)
  ; comment2 = pseq (tokens "{-#") (ppost (many (noneOf [newlineC,carriageReturnC])) eol)
  }

-- | Note: this accepts "eof"!
emptyLineL :: Lexer Unit
emptyLineL = pseq spaces0 eol

type Block = List LToken

-- | Parser a line and all following indented lines
blockL :: Lexer Block
blockL = worker1 where
  { line = many1 (locatedL lexemeL)
  ; worker  = pbind eolIndent (\k -> ifte (gt k 0) (option Nil worker1) (preturn Nil))
  ; worker1 = pbind line      (\ls1 -> pbind worker (\ls2 -> preturn (append ls1 ls2)))
  }

blockOrCommentL :: Lexer (Maybe Block)
blockOrCommentL = choice
  [ preplace Nothing commentL
  , preplace Nothing emptyLineL
  , pfmap    Just    blockL
  ]

programL :: Lexer (List Block)
programL = pfmap catMaybes (manyTill eof blockOrCommentL)

lexer :: String -> List Block
lexer input = runParser_ programL (addLocations input)

--------------------------------------------------------------------------------
-- ** Surface syntax

type Name = String

data Defin a = Defin Name a deriving Show
type DefinE  = Defin Expr

fmapDefin :: (a -> b) -> Defin a -> Defin b
fmapDefin f defin = case defin of { Defin n x -> Defin n (f x) }

definedName :: Defin a -> Name
definedName defin = case defin of { Defin n _ -> n }

definedWhat :: Defin a -> a
definedWhat defin = case defin of { Defin _ e -> e }

type Program a = List (Defin a)

-- | We \"parse\" (well, recognize) type declarations, data declarations,
-- type synonyms and imports, but we ignore them; this is simply so that the
-- this source code can be a valid Haskell program and self-hosting at the
-- same time.
data TopLevel
  = TopDefin    DefinE
  | TopTyDecl   Name (List Token)
  | TopDataDecl (List Token)
  | TopTyAlias  (List Token)
  | TopImport   (List Token)
  | TopInclude  FilePath
  | TopModule   (List Token)
  deriving Show

mbDefin :: TopLevel -> Maybe DefinE
mbDefin toplev = case toplev of { TopDefin def -> Just def ; _ -> Nothing }

-- programToExpr :: Program -> Expr
-- programToExpr defs = PrgE defs (VarE "main")

data Expr
  = VarE  Name
  | AppE  Expr Expr
  | LamE  Name Expr
  | LetE  (List DefinE) Expr
  | PrgE  (List DefinE) Expr
  | CaseE Expr (List BranchE)
  | LitE  Literal
  | ListE (List Expr)
  | PrimE PrimOp (List Expr)
  deriving Show

data BranchE
  = BranchE Name (List Name) Expr
  | DefaultE Expr
  deriving Show

-- data BranchE
--   = BranchE Pattern Expr
--   deriving Show

lamsE :: List Name -> Expr -> Expr
lamsE args body = case args of { Nil -> body ; Cons v vs -> LamE v (lamsE vs body) }

appsE :: Expr -> List Expr -> Expr
appsE fun  args = case args of { Nil -> fun  ; Cons t ts -> appsE (AppE fun t) ts  }

listAppsE :: List Expr -> Expr
listAppsE  list = case list of { Cons f args -> appsE f args ; Nil -> error "listAppsE" }

--------------------------------------------------------------------------------
-- ** TODO: Pattern compiler 

data Pattern
  = SimP Name (List Name)         -- ^ simple pattern
  | AppP Name (List Pattern)      -- ^ constructor pattern
  | VarP Name                     -- ^ variable pattern
  | WildP                         -- ^ wildcard patterns
  | ListP (List Pattern)          -- ^ list pattern
  deriving Show

patternHead :: Pattern -> Maybe Name
patternHead pat = case pat of
  SimP con _list -> Just con
  AppP con _list -> Just con
  _              -> Nothing

-- -- | We translate complex pattern into iterated matching of simple patterns
-- patternCompiler :: List BranchE -> List BranchE
-- patternCompiler

--------------------------------------------------------------------------------
-- ** Primops

data Prim
  = Negate | Plus | Minus | Times | Div | Mod | Chr | Ord 
  | BitAnd | BitOr | BitXor | ShiftL | ShiftR
  | IFTE | Not | And | Or | GenEQ | IntEQ | IntLT | IntLE
  | GetChar | PutChar | GetArg | Exit | Error 
  | OpenFile | HClose | HGetChar | HPutChar | StdIn | StdOut | StdErr
  deriving (Eq,Show)

isLazyPrim :: Prim -> Bool
isLazyPrim prim = case prim of
  { IFTE -> True
  ; And  -> True
  ; Or   -> True 
  ; _    -> False }

showPrim :: Prim -> String
showPrim prim = case prim of
  { Negate   -> "Negate"   ; Plus     -> "Plus"     ; Minus   -> "Minus"
  ; Times    -> "Times"    ; Div      -> "Div"      ; Mod     -> "Mod"
  ; BitAnd   -> "BitAnd"   ; BitOr    -> "BitOr"    ; BitXor  -> "BitXor"
  ; ShiftL   -> "ShiftL"   ; ShiftR   -> "ShiftR"        
  ; Chr      -> "Chr"      ; Ord      -> "Ord"      ; IFTE    -> "IFTE"
  ; Not      -> "Not"      ; And      -> "And"      ; Or      -> "Or"
  ; IntEQ    -> "IntEQ"    ; IntLT    -> "IntLT"    ; IntLE   -> "IntLE"
  ; GenEQ    -> "GenEQ"    ; Error    -> "Error"    ; Exit    -> "Exit" 
  ; GetChar  -> "GetChar"  ; PutChar  -> "PutChar"  ; GetArg  -> "GetArg" 
  ; StdIn    -> "StdIn"    ; StdOut   -> "StdOut"   ; StdErr  -> "StdErr" 
  ; HGetChar -> "HGetChar" ; HPutChar -> "HPutChar" ; HClose  -> "HClose" 
  ; OpenFile -> "OpenFile" }

type Arity = Int

data PrimOp = PrimOp Arity Prim deriving Show

primops :: Trie PrimOp
primops = trieFromList
  [ Pair "error"     (PrimOp 1  Error   )
  , Pair "negate"    (PrimOp 1  Negate  )
  , Pair "plus"      (PrimOp 2  Plus    )
  , Pair "minus"     (PrimOp 2  Minus   )
  , Pair "times"     (PrimOp 2  Times   )
  , Pair "div"       (PrimOp 2  Div     )
  , Pair "mod"       (PrimOp 2  Mod     )
  , Pair "bitAnd"    (PrimOp 2  BitAnd  ) 
  , Pair "bitOr"     (PrimOp 2  BitOr   )
  , Pair "bitXor"    (PrimOp 2  BitXor  ) 
  , Pair "shiftL"    (PrimOp 2  ShiftL  )
  , Pair "shiftR"    (PrimOp 2  ShiftR  )
  , Pair "chr"       (PrimOp 1  Chr     )
  , Pair "ord"       (PrimOp 1  Ord     )
  , Pair "ifte"      (PrimOp 3  IFTE    )
  , Pair "not"       (PrimOp 1  Not     )
  , Pair "and"       (PrimOp 2  And     )
  , Pair "or"        (PrimOp 2  Or      )
  , Pair "geq"       (PrimOp 2  GenEQ   )
  , Pair "eq"        (PrimOp 2  IntEQ   )
  , Pair "lt"        (PrimOp 2  IntLT   )
  , Pair "le"        (PrimOp 2  IntLE   )
  , Pair "getChar#"  (PrimOp 1  GetChar )
  , Pair "putChar#"  (PrimOp 1  PutChar )
  , Pair "getArg#"   (PrimOp 1  GetArg  )
  , Pair "exit#"     (PrimOp 1  Exit    )
  , Pair "openFile#" (PrimOp 2  OpenFile)
  , Pair "hClose#"   (PrimOp 1  HClose  )
  , Pair "hGetChar#" (PrimOp 1  HGetChar)
  , Pair "hPutChar#" (PrimOp 2  HPutChar)
  , Pair "stdin"     (PrimOp 0  StdIn   )
  , Pair "stdout"    (PrimOp 0  StdOut  )
  , Pair "stderr"    (PrimOp 0  StdErr  )
  ]

-- | From @((f x) y) z@ we create the list [f,x,y,z]
recogAppsE :: Expr -> List Expr
recogAppsE = compose reverse go where
  { go expr = case expr of { AppE f x -> Cons x (go f)  ; _ -> singleton expr } }

tmpVars :: List Name
tmpVars = ["x1","x2","x3","x4","x5"]
-- tmpVars = map (\i -> append "x" (showInt i)) (rangeFrom 1 5)

-- | Saturate primop application
saturatePrimApp :: PrimOp -> List Expr -> Expr
saturatePrimApp primop args = case primop of { PrimOp arity prim -> case compare nargs arity of
  { EQ ->        PrimE primop args
  ; GT -> appsE (PrimE primop (take arity args)) (drop arity args)
  ; LT -> let { vars = take (minus arity nargs) tmpVars }
          in  lamsE vars (PrimE primop (append args (map VarE vars)))
  } }
  where { nargs = length args }

-- | Recognize primop applications, and saturate them if necessary
recogPrimApps :: Program Expr -> Program Expr
recogPrimApps prg = map (fmapDefin recogPrimApps1) prg

-- | Recognize primop applications, and saturate them if necessary
recogPrimApps1 :: Expr -> Expr
recogPrimApps1 = go where
  { goVar name = case trieLookup name primops of
      { Nothing        -> VarE name
      ; Just primop    -> saturatePrimApp primop [] }
  ; go expr = case expr of
      { VarE name      -> goVar name
      ; AppE _ _       -> case recogAppsE expr of { Cons f args -> case f of
          { VarE n       -> case trieLookup n primops of
              { Nothing     -> appsE (VarE n)         (map go args)
              ; Just primop -> saturatePrimApp primop (map go args) }
          ; _            -> appsE (go    f) (map go args) } }
      ; LamE arg  body -> LamE  arg  (go body)
      ; LetE defs body -> LetE  (map goDefin defs) (go body)
      ; PrgE defs body -> PrgE  (map goDefin defs) (go body)
      ; CaseE what brs -> CaseE (go what) (map goBranch brs)
      ; ListE exprs    -> ListE (map go exprs)
      ; _              -> expr }
  ; goBranch branch = case branch of
      { BranchE con args rhs -> BranchE con args (go rhs)
      ; DefaultE         rhs -> DefaultE         (go rhs) }
  ; goDefin defin = case defin of
      { Defin name expr -> Defin name (go expr) } }

--------------------------------------------------------------------------------
-- ** The parser

type Parse a = Parser Token a

parseTopLevelBlock :: Block -> TopLevel
parseTopLevelBlock tokens = runParser_ topLevelP (filterWhite tokens)

filterWhite :: Block -> Block
filterWhite = filter cond where { cond ltok = isNotWhite (located ltok) }

keywords :: List String
keywords = [ "where" , "case" , "of" , "let" , "in" , "module" , "import" , "include" , "data" , "type" ]

isKeyword :: String -> Bool
isKeyword str = elem str keywords

topLevelP :: Parse TopLevel
topLevelP = choice
  [ tyAliasP
  , dataDeclP
  , importP
  , includeP
  , moduleP
  , tyDeclP
  , pfmap TopDefin definP
  ]

tyDeclP :: Parse TopLevel
tyDeclP = pbind  varP            (\name ->
          pbind (specP HasType ) (\_    ->
          pbind (many1 anyToken) (\toks -> preturn (TopTyDecl name toks) )))

dataDeclP :: Parse TopLevel
dataDeclP = pbind (keywordP "data") (\_ ->
            pbind (many1 anyToken ) (\toks -> preturn (TopDataDecl toks) ))

tyAliasP :: Parse TopLevel
tyAliasP = pbind (keywordP "type") (\_ ->
           pbind (many1 anyToken ) (\toks -> preturn (TopTyAlias toks) ))

-- haskell import
importP :: Parse TopLevel
importP = pbind (keywordP "import") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopImport toks) ))

-- our C-style include
includeP :: Parse TopLevel
includeP = pbind (keywordP "include") (\_ ->
           pbind (accept mbStrLit   ) (\fname -> preturn (TopInclude fname) ))

moduleP :: Parse TopLevel
moduleP = pbind (keywordP "module") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopModule toks) ))

definP :: Parse DefinE
definP = pbind varP              (\name ->
         pbind (many varP)       (\args ->
         pbind (specP EqualSign) (\_    ->
         pbind exprP             (\body -> preturn (Defin name (lamsE args body)) ))))

exprP :: Parse Expr
exprP = pbind nakedExprP             (\expr ->
        pbind (optional whereBlockP) (\mb   ->
        preturn (case mb of { Nothing -> expr ; Just defs -> LetE defs expr } )))

whereBlockP :: Parse (List DefinE)
whereBlockP = pbind (keywordP "where") (\_ -> blockP)

-- | Here \"naked\" means without a where block
nakedExprP :: Parse Expr
nakedExprP = choice
  [ lamExprP
  , pfmap listAppsE (many1 atomP)
  ]

-- | We need an explicit eta-expansion here so that it doesn't loop in GHCi
-- (and probably also itself)
atomP :: Parse Expr
atomP what = choice
  [ inParensP exprP
  , pfmap LitE  literalP
  , pfmap ListE listExprP
  , caseExprP
  , letExprP
  , pfmap VarE varP
  ] what

specP :: Special -> Parse Special
specP spec = preplace spec (token (SpecTok spec))

literalP :: Parse Literal
literalP = accept mbLit

-- capitalIdentP :: Parse Name
-- capitalIdentP = accept mbVarU

identP :: Parse Name
identP = accept mbVar

-- | This does not accepts they keywords, but accepts constructors
varP :: Parse Name
varP = pbind identP (\v -> ifte (isKeyword v) pfail (preturn v))

-- | This only accept uppercase identifiers
conP :: Parse Name
conP = accept mbVarU

keywordP :: String -> Parse String
keywordP word = pbind identP (\v -> ifte (geq v word) (preturn word) pfail)

inParensP :: Parse a -> Parse a
inParensP p = pbind (specP LParen) (\_ ->
              pbind p              (\x ->
              pbind (specP RParen) (\_ -> preturn x)))

listExprP  :: Parse (List Expr   )
tupleExprP :: Parse (List Expr   )
blockP     :: Parse (List DefinE )
branchesP  :: Parse (List BranchE)

listExprP  = pbind (specP LBracket) (\_ -> sepEndBy (specP Comma    ) (specP RBracket) exprP  )
tupleExprP = pbind (specP LParen  ) (\_ -> sepEndBy (specP Comma    ) (specP RParen  ) exprP  )
blockP     = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) definP )
branchesP  = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) branchP)

patternP :: Parse Pattern
patternP = naked where
  { naked what = choice [ wild , var , inParensP patternP , apps ] what
  ; safe  what = choice [ wild , var , inParensP patternP , con  ] what
  ; wild  = pbind (keywordP "_" ) (\_    -> preturn  WildP  )
  ; var   = pbind (accept mbVarL) (\v    -> preturn (VarP v))
  ; con   = pbind  conP           (\con  -> preturn (AppP con Nil))
  ; apps  = pbind  conP           (\con  ->
            pbind (many safe    ) (\args -> preturn (AppP con args)))
  }

branchP :: Parse BranchE
branchP = alternative defaultBranchP branchP'

branchP' :: Parse BranchE
branchP' = pbind conP          (\con  ->
           pbind (many varP  ) (\args ->
           pbind (specP Arrow) (\_    ->
           pbind (exprP      ) (\body -> preturn (BranchE con args body)))))

defaultBranchP :: Parse BranchE
defaultBranchP = pbind (keywordP "_") (\_    ->
                 pbind (specP Arrow ) (\_    ->
                 pbind (exprP       ) (\body -> preturn (DefaultE body))))

lamExprP :: Parse Expr
lamExprP =
  pbind (specP Lambda) (\_    ->
  pbind (many1 varP  ) (\args ->
  pbind (specP Arrow ) (\_    ->
  pbind exprP          (\body -> preturn (lamsE args body)))))

letExprP :: Parse Expr
letExprP = pbind (keywordP "let") (\_    ->
           pbind (blockP        ) (\defs ->
           pbind (keywordP "in" ) (\_    ->
           pbind (exprP         ) (\expr -> preturn (LetE defs expr)))))

caseExprP :: Parse Expr
caseExprP = pbind (keywordP "case") (\_    ->
            pbind (exprP          ) (\expr ->
            pbind (keywordP "of"  ) (\_    ->
            pbind (branchesP      ) (\brs  -> preturn (CaseE expr brs)))))

--------------------------------------------------------------------------------
-- * Core language

-- | De Bruijn index
type Idx = Int

-- | Constructor index
type Con = Int

-- | We want to keep names for debugging \/ pretty printing
data Named a = Named Name a deriving Show

nfmap :: (a -> b) -> Named a -> Named b
nfmap f named = case named of { Named name x -> Named name (f x) }

forgetName :: Named a -> a
forgetName x = case x of { Named _ y -> y }

nameOf :: Named a -> String
nameOf x = case x of { Named n _ -> n }

--------------------------------------------------------------------------------
-- Atoms

-- | Variables can be a de Bruijn index, or a top-level definition
-- (the latter is only an optimization, so we don't have to allocate
-- closures for static functions)
data Var
  = IdxV Idx
  | TopV Static
  deriving Show

prettyVar :: Var -> String
prettyVar var = case var of 
  { IdxV i -> concat [  "de Bruijn (" , showInt i , ")" ] 
  ; TopV j -> concat [ "static fun (" , showInt j , ")" ] }

prettyAtom :: Atom -> String
prettyAtom atom = case atom of
  { VarA var  -> prettyVar (forgetName var)
  ; ConA ncon -> nameOf ncon
  ; KstA lit  -> showLiteral lit }

showLiteral :: Literal -> String
showLiteral lit = case lit of
  { IntL n -> showInt  n
  ; ChrL c -> showChar c
  ; StrL s -> doubleQuoteString s }

-- | Things which can be applied, case-branched, passed to primops
-- TODO: refactor to use this
data Atom
  = VarA (Named Var)
  | ConA (Named Con)
  | KstA Literal
  deriving Show

-- type Atom = Named Var

--------------------------------------------------------------------------------
-- Terms

-- pattern VarT nvar = AtmT (VarA nvar)
-- pattern ConT ncon = AtmT (ConA ncon)
-- pattern KstT lit  = AtmT (KstA lit )

data Term
--  = VarT (Named Var )
--  | ConT (Named Con )
--  | KstT Literal
  = AtmT Atom 
  | LamT (Named Term)
  | AppT Term Atom
  | PriT PrimOp (List Atom)
  | LZPT PrimOp (List Term)
  | LetT Term Term
  | RecT Int (List (Named Term)) Term
  | PrgT Int (List (Named Term)) Term
  | CasT Atom (List BranchT)
  deriving Show

data BranchT
  = BranchT (Named Con) Int Term
  | DefaultT Term
  deriving Show

transformAtom :: (Level -> Atom -> Atom) -> Level -> Term -> Term
transformAtom f = go where 
  { go level term = case term of
    { AtmT a -> AtmT (f level a)
--    { VarT a        -> VarT (f level a)
--    ; ConT _        -> term
--    ; KstT _        -> term
    ; LamT nt       -> LamT (nfmap (go (inc level)) nt)
    ; AppT t a      -> AppT (go level t) (f level a)
    ; PriT p as     -> PriT p (map (f  level) as)
    ; LZPT p ts     -> LZPT p (map (go level) ts)
    ; LetT t1 t2    -> LetT (go level t1) (go (inc level) t2)
    ; RecT n nts t  -> let { level' = plus level n } in RecT n (map (nfmap (go level')) nts) (go level' t)
    ; CasT a brs    -> CasT (f level a) (map (goBranch level) brs) }
  ; goBranch level branch = case branch of  
    { BranchT c n t -> BranchT c n (go (plus level n) t)
    ; DefaultT    t -> DefaultT    (go       level t   ) } }

-- namedTermSize :: Named Term -> Int
-- namedTermSize named = case named of { Named _ tm -> termSize tm }

termSize :: Term -> Int
termSize term = go term where 
  { goNamed named = case named of { Named _ tm -> go tm }
  ; go term = case term of
    { AtmT _       -> 1
--    { VarT _       -> 1
--    ; ConT _       -> 1
--    ; KstT _       -> 1
    ; LamT nbody   -> inc (goNamed nbody)
    ; AppT tm v    -> inc (go tm)
    ; PriT _ _     -> 1
    ; LZPT _ ts    -> inc (sum (map go ts))
    ; LetT t1 t2   -> inc (plus (go t1) (go t2))
    ; RecT _ ls tm -> inc (plus (sum (map goNamed ls)) (go tm))
    ; CasT _ brs   -> inc (sum (map goBranch brs)) }
  ; goBranch br = case br of
    { DefaultT tm    -> go tm
    ; BranchT _ k tm -> plus k (go tm) } }
   
exprToCore :: DataConTable -> Scope -> Expr -> Term
exprToCore dconTable iniScope expr = scopeCheck dconTable iniScope (recogPrimApps1 expr)

data CoreProgram 
  = CorePrg (Program Term) Term 
  deriving Show

programToCoreProgram :: Program Expr -> CoreProgram
programToCoreProgram defins = CorePrg (map worker defins) main where
  { topLevScope = trieFromList (zipWithIndex (\n i -> Pair n (TopL i)) (map definedName defins))
  ; dconTable   = collectDataCons defins
  ; worker def  = case def of { Defin name expr -> Defin name (exprToCore dconTable topLevScope expr) } 
  ; no_main_err = \_ -> error "entry point `main` not found" 
  ; main = case trieLookup "main" topLevScope of { Just varl -> case varl of
      { TopL k -> AtmT (VarA (Named "main" (TopV k))) ; _ -> no_main_err Unit } ; _ -> no_main_err Unit } } 

--------------------------------------------------------------------------------
-- ** Data constructors

isDCon :: Name -> Bool
isDCon name = isUpper (head name)

-- | Mapping constructor names to constructor tags
type DataConTable = Trie Con

con_False   = 0
con_True    = 1
con_Unit    = 2
con_Nil     = 3
con_Cons    = 4
con_Nothing = 5
con_Just    = 6
con_ReadMode      = 7
con_WriteMode     = 8
con_AppendMode    = 9
con_ReadWriteMode = 10

type DConState = Pair Int DataConTable

initialDConState :: DConState
initialDConState = Pair 11 (trieFromList predefinedDataCons)

predefinedDataCons :: List (Pair String Int)
predefinedDataCons =
  [ Pair "False" con_False , Pair "True" con_True , Pair "Unit"    con_Unit
  , Pair "Nil"   con_Nil   , Pair "Cons" con_Cons , Pair "Nothing" con_Nothing , Pair "Just" con_Just 
  , Pair "ReadMode"   con_ReadMode   , Pair "WriteMode"     con_WriteMode        
  , Pair "AppendMode" con_AppendMode , Pair "ReadWriteMode" con_ReadWriteMode ]

-- | Collect data constructors from the source.
--
-- Encoding of constructors tags:
--
-- *  0 = False
-- *  1 = True
-- *  2 = Unit
-- *  3 = Nil
-- *  4 = Cons
-- *  5 = Nothing
-- *  6 = Just
-- *  7 = ReadMode
-- *  8 = WriteMode
-- *  9 = AppendMode
-- * 10 = ReadWriteMode
-- * 11.. = user defined constructors
--
-- We need to fix Int, Char, False, True, Unit, Nil, Cons, Just and Nothing
-- and the file modes because the primops use them
--
collectDataCons :: Program Expr -> DataConTable
collectDataCons defins = snd (execState action initialDConState) where
  { action = smapM_ collectDataConsWorker (map definedWhat defins) }

collectDataConsWorker :: Expr -> State DConState Unit
collectDataConsWorker expr = go expr where
  { insert name = sbind sget (\pair -> case pair of { Pair n table -> case trieLookup name table of
    { Just k  -> sreturn Unit
    ; Nothing -> sput (Pair (inc n) (trieInsert name n table)) } })
  ; go expr = case expr of
    { VarE name -> case isDCon name of { False -> sreturn Unit ; True -> insert name }
    ; AppE e1 e2  -> sseq (go e1) (go e2)
    ; LamE _ body -> go body
    ; LetE defs body -> sseq
        (smapM_ (\defin -> case defin of { Defin _ rhs -> go rhs }) defs )
        (go body)
    ; CaseE e branches -> sseq (go e) (smapM_ (\br -> case br of
        { BranchE con _ rhs -> sbind (insert con) (\_ -> go rhs)
        ; DefaultE      rhs -> go rhs }) branches)
    ; LitE _     -> sreturn Unit
    ; ListE list -> smapM_ go list
    ; PrimE _ as -> smapM_ go as
    } }

--------------------------------------------------------------------------------
-- ** Scope checking / conversion to core

-- | De Bruijn level
type Level = Int

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
    ; AppE e1 e2 -> case mbAtom level scope e2 of
        { Just atom -> AppT (go level scope e1) atom
        ; Nothing   -> LetT (go level scope e2) (AppT (go (inc level) scope e1) (VarA (Named "letx" (IdxV 0)))) }
    ; LamE  name body -> LamT (Named name (go (inc level) (trieInsert name (LevL level) scope) body))
    ; LetE  defs body -> let { n = length defs ; level' = plus level n
        ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
        ; scope' = foldl f scope (zip (map definedName defs) (rangeFrom level n))
        } in RecT n (map (goDefin level' scope') defs) (go level' scope' body)
-- TODO: optimize for nonrecursive lets ?
    ; CaseE what brs -> case mbAtom level scope what of
        { Just atom -> goCase level scope atom brs
        ; Nothing   -> LetT (go level scope what) (goCase (inc level) scope (VarA (Named "scrut" (IdxV 0))) brs) }
    ; LitE  lit -> case lit of
        { StrL cs -> go level scope (ListE (map (\x -> LitE (ChrL x)) cs))
        ; _       -> AtmT (KstA lit) }
    ; ListE exprs -> case exprs of 
        { Nil       -> AtmT (ConA (Named "Nil" con_Nil))
--        ; Cons e es -> AppT (AppT (ConT (Named "Cons" conCons)) (go level scope e)) (go level scope (ListE es)) }
        ; Cons e es -> go level scope (AppE (AppE (VarE "Cons") e) (ListE es)) }
    ; PrimE prim args -> case prim of { PrimOp _arity pri -> case isLazyPrim pri of 
        { False -> goArgs level scope args (PriT prim 
            (zipWithIndex (\i j -> VarA (Named (appendInt "name" j) (IdxV i))) (reverse (range (length args))) ))
        ; True  -> LZPT prim (map (go level scope) args) }}
    }
  ; goArgs level scope args body = case args of 
      { Nil            -> body 
      ; Cons this rest -> LetT (go level scope this) (goArgs (inc level) scope rest body) }
--      TODO: this is inefficient when args are already Vars
  ; goDefin level scope defin = case defin of { Defin name what -> Named name (go level scope what) }
  ; goCase level scope var branches = CasT var (map goBranch branches) where
    { goBranch branch = case branch of
        { DefaultE         rhs -> DefaultT (go level scope rhs)
        ; BranchE con args rhs -> let { n = length args ; level' = plus level n
          ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name (LevL j) scp }
          ; scope' = foldl f scope (zip args (rangeFrom level n))
          } in BranchT (Named con (lookupCon dcontable con)) n (go level' scope' rhs) } } }

--------------------------------------------------------------------------------
-- * The interpreter
-- ** Runtime values

-- | Note: for recursive lets, we need some delaying mechanism; currently
-- this is done using the @ThkV@ (Thunk) constructor (which was added only
-- for this purpose).
data Value
  = IntV Int
  | ChrV Char
  | ConV Con (List Value)
  | LamV (Value -> Value)
  | ThkV Env Term

-- -- | Force thunks
-- forceValue :: Value -> Value
-- forceValue val = case val of { ThkV env tm -> eval env tm ; _ -> val }

-- showValue :: Value -> String
-- showValue value = case value of
--   { IntV n -> showInt n
--   ; ChrV c -> quoteChar c
--   ; ConV con args -> let { tag = appendInt "Con#" con } in case args of { Nil -> tag
--     ; Cons _ _ -> parenString (unwords (Cons tag (map showValue args))) }
--   ; LamV   _ -> "<lambda>"
--   ; ThkV env tm -> showValue (eval env tm)
--   }
-- 
-- eqValue :: Value -> Value -> Bool
-- eqValue val1 val2 = case val1 of
--   { IntV i1 -> case val2 of { IntV i2 ->  eq i1 i2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
--   ; ChrV c1 -> case val2 of { ChrV c2 -> ceq c1 c2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
--   ; ConV con1 args1 -> case val2 of
--       { ConV con2 args2 -> and3 (eq con1 con2) (eq (length args1) (length args2))
--                                 (andList (zipWith eqValue args1 args2))
--       ; ThkV env2 tm2   -> eqValue val1 (eval env2 tm2)
--       ; _ -> False }
--   ; LamV _        -> False
--   ; ThkV env1 tm1 -> eqValue (eval env1 tm1) val2
--   }

boolToValue :: Bool -> Value
boolToValue b = ifte b (ConV con_True Nil) (ConV con_False Nil)

valueToBool :: Value -> Bool
valueToBool val = case val of { ConV con args -> eq con con_True ; _ -> error "not a boolean" }

intToValue :: Int -> Value
intToValue = IntV

valueToInt :: Value -> Int
valueToInt val = case val of { IntV x -> x ; _ -> error "not an integer" }

charToValue :: Char -> Value
charToValue = ChrV

maybeCharToValue :: Maybe Char -> Value
maybeCharToValue mb = case mb of { Nothing -> ConV con_Nothing Nil ; Just c -> ConV con_Just (singleton (ChrV c)) }

valueToChar :: Value -> Char
valueToChar val = case val of { ChrV c -> c ; _ -> error "not a character" }

unitToValue :: Unit -> Value
unitToValue Unit = ConV con_Unit Nil

valueToUnit :: Value -> Unit
valueToUnit val = case val of { ConV con _ -> ifte (eq con con_Unit) Unit err ; _ -> err } where
  { err = error "not a unit" }

listToValue :: List Value -> Value
listToValue list = case list of { Nil -> ConV con_Nil Nil
  ; Cons x xs -> ConV con_Cons [ x , listToValue xs ] }

valueToList :: Value -> List Value
valueToList value = case value of
  { ConV con args -> ifte (neq con con_Cons) Nil
      (case mbPair args of { Nothing -> Nil ; Just pair -> case pair of
        { Pair u v -> Cons u (valueToList v) } } ) }

stringToValue :: String -> Value
stringToValue = compose listToValue (map charToValue)

valueToString :: Value -> String
valueToString = compose (map valueToChar) valueToList

--------------------------------------------------------------------------------
-- ** Evaluating primops

evalfunII :: (Int -> Int) -> Value -> Value
evalfunII f v1 = intToValue (f (valueToInt v1))

evalfunIII :: (Int -> Int -> Int) -> Value -> Value -> Value
evalfunIII f v1 v2 = intToValue (f (valueToInt v1) (valueToInt v2))

evalfunIIB :: (Int -> Int -> Bool) -> Value -> Value -> Value
evalfunIIB f v1 v2 = boolToValue (f (valueToInt v1) (valueToInt v2))

evalfunBB :: (Bool -> Bool) -> Value -> Value
evalfunBB f v1 = boolToValue (f (valueToBool v1))

evalfunBBB :: (Bool -> Bool -> Bool) -> Value -> Value -> Value
evalfunBBB f v1 v2 = boolToValue (f (valueToBool v1) (valueToBool v2))

unary   :: List a -> (a -> b)           -> b
binary  :: List a -> (a -> a -> b)      -> b
ternary :: List a -> (a -> a -> a -> b) -> b
unary   args f = case args of { Cons x xs -> f x             ; Nil -> error "unary: not enough arguments"   }
binary  args f = case args of { Cons x xs -> unary  xs (f x) ; Nil -> error "binary: not enough arguments"  }
ternary args f = case args of { Cons x xs -> binary xs (f x) ; Nil -> error "ternary: not enough arguments" }

evalPrim :: Prim -> List Value -> Value
evalPrim prim args = case prim of
  { Error   -> unary   args (compose error valueToString)
  ; Negate  -> unary   args (evalfunII  negate)
  ; Plus    -> binary  args (evalfunIII plus  )
  ; Minus   -> binary  args (evalfunIII minus )
  ; Times   -> binary  args (evalfunIII times )
  ; Div     -> binary  args (evalfunIII div   )
  ; Mod     -> binary  args (evalfunIII mod   )
  ; Chr     -> unary   args (compose3 charToValue chr valueToInt )
  ; Ord     -> unary   args (compose3 intToValue  ord valueToChar)
--  ; IFTE    -> error "ifte: this has to be implemented somewhere else because of lazyness"
--  ; And     -> binary  args (evalfunBBB and )
--  ; Or      -> binary  args (evalfunBBB or  )
  ; Not     -> unary   args (evalfunBB  not )
--  ; GenEQ   -> binary  args (\x y -> boolToValue (eqValue x y))
  ; IntEQ   -> binary  args (evalfunIIB eq  )
  ; IntLT   -> binary  args (evalfunIIB lt  )
  ; IntLE   -> binary  args (evalfunIIB le  )
  ; GetChar -> unary   args (compose3 maybeCharToValue (\_ -> getChar   Unit) valueToUnit)
  ; PutChar -> unary   args (compose3 unitToValue      (\c -> putChar c Unit) valueToChar)
  ; Exit    -> unary   args (compose3 unitToValue      (\k -> exit    k Unit) valueToInt )
--  ; GetArg  -> ??? where should the interpreter get the arguments ???
--  ; IsEOF   -> unary   args (compose3 boolToValue isEOF   valueToUnit)
  ; _       -> error "evalPrim: unimplemented primop"
  }

--------------------------------------------------------------------------------
-- ** The evaluator

-- in reverse order as usual
type Env = List Value

-- evalVar :: Env -> Idx -> Value
-- evalVar env idx = forceValue (index idx env)
-- 
-- eval :: Env -> Term -> Value
-- eval env term = case term of
--   { VarT idx     -> evalVar env (forgetName idx)
--   ; ConT con     -> ConV (forgetName con) Nil
--   ; AppT e1 a2   -> case eval env e1 of
--     { LamV fun      -> fun                 (evalVar env (forgetName a2))
--     ; ConV con args -> ConV con (snoc args (evalVar env (forgetName a2)))
--     ; _             -> error "application to non-lambda (int/char)" }
--   ; PriT primop vs -> case primop of { PrimOp _arity prim -> evalPrim prim (map (evalVar env) vs) }
--   ; LZPT primop ts -> case primop of { PrimOp _arity prim -> case prim of
--     { IFTE -> ternary ts (lazyIFTE env)
--     ; And  -> binary  ts (lazyAnd  env)
--     ; Or   -> binary  ts (lazyOr   env)
--     ; _    -> error "unrecognized lazy primop" }}
--   ; LamT body    -> LamV (\x -> eval (Cons x env) (forgetName body))
--   ; CasT var brs -> case forceValue (index var env) of
--     { ConV con args -> matchCon env con args brs
--     ; _             -> error "branching on a non-constructor (lambda)" }
--   ; RecT n ls tm -> let { env' = append (reverse (map (mkThunk env') ls)) env } in eval env' tm
--   ; KstT lit     -> case lit of
--     { IntL k       -> IntV k
--     ; ChrL c       -> ChrV c
--     ; StrL _       -> error "string literals should not appear in core" }
--   } 
--   where { mkThunk env1 named = case named of { Named name body -> ThkV env1 body } }
-- 
-- lazyIFTE :: Env -> Term -> Term -> Term -> Value
-- lazyIFTE env tb tx ty = let { vb = eval env tb } in ifte (valueToBool vb) (eval env tx) (eval env ty)
-- 
-- lazyAnd :: Env -> Term -> Term -> Value
-- lazyAnd env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (eval env t2) (boolToValue False)
-- 
-- lazyOr :: Env -> Term -> Term -> Value
-- lazyOr env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (boolToValue True) (eval env t2)
-- 
-- matchCon :: Env -> Con -> List Value -> List BranchT -> Value
-- matchCon env con args = go where
--   { nargs = length args
--   ; go branches = case branches of
--     { Nil -> error "non-exhaustive patterns in case"
--     ; Cons this rest -> case this of
--       { DefaultT rhs            -> eval env rhs
--       ; BranchT bcon bnargs rhs -> ifte (and (eq con (forgetName bcon)) (eq nargs bnargs))
--           (eval (append (reverse args) env) rhs)
--           (go rest) } } }

--------------------------------------------------------------------------------
-- * The compiler
-- ** Closure conversion

-- | Index of statically known functions (and thunks); starts from zero
type Static = Int

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
  ; goVar  level var = case var of { TopV _ -> setEmpty;
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
            ; TopV top -> VarA (Named name (TopV top)) }}
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

doInline :: Term -> Bool
doInline _ = False
--doInline tm = case tm of
--  { LamT _     -> False
--  ; _          -> le (termSize tm) 25 }

termToClosure :: Int -> Name -> Level -> Term -> ClosM ClosureF
termToClosure nstatic name level term = ifte (doInline term) 
  (termToInlineClosure nstatic name level term) 
  (termToStaticClosure nstatic name level term)

-- | The int list is the mapping from the source code top-level functions
-- to the generated code top-level functions
data LiftedProgram = LProgram (List TopLev) (List Int) Lifted deriving Show

coreProgramToLifted :: CoreProgram -> LiftedProgram
coreProgramToLifted coreprg = case coreprg of { CorePrg defins mainTerm -> let
  { nstatic = length defins  
  ; action1 = sforM defins (\defin -> case defin of { Defin name term -> sfmap closureIndex (termToStaticClosure nstatic name 0 term) })
  ; action2 = closureConvert nstatic "main" 0 0 mainTerm  
  ; action  = sliftA2 Pair action1 action2
  } in case runState action Nil of { Pair toplist pair2 -> 
         case pair2 of { Pair idxlist main -> LProgram (reverse toplist) idxlist main } } }

-- coreToLifted :: Term -> LiftedProgram
-- coreToLifted term = case runState (handleTopLetRec term) Nil of { Pair toplist pair2 -> 
--   case pair2 of { Pair idxlist main -> LProgram (reverse toplist) idxlist main }}
-- 
-- -- | The top-level letrec is handled specially (we want static functions)
-- handleTopLetRec :: List (Defin Term) -> ClosM (Pair (List Static) Lifted)
-- handleTopLetRec defins = let { nstatic = length defins ; main = Top} in 
-- term = case term of { PrgT nstatic toplevs main -> sliftA2 Pair
--   (sforM toplevs (\named -> case named of { Named name term -> sfmap closureIndex (termToStaticClosure nstatic name 0 term) }))
--   (closureConvert nstatic "main" 0 0 main) }

addPrefix :: Name -> Name -> Name
addPrefix prefix name = append3 prefix "/" name

-- closureConvert :: Int -> Name -> Level -> ClosEnv -> Level -> Term -> ClosM Lifted
-- closureConvert nstatic nameprefix boundary closEnv = go where

closureConvert :: Int -> Name -> Level -> Level -> Term -> ClosM Lifted
closureConvert nstatic nameprefix boundary = go where
  { prefixed name = addPrefix nameprefix name
  ; goVar level idx = IdxV idx
--  ; goVar level idx = let { j = minus level (inc idx) } in 
--      ifte (ge j boundary) (IdxV idx)
--        (case mapLookup j closEnv of
--          { Nothing -> error "closureConvert: fatal error: variable not in the pruned environment"
--          ; Just m  -> let { i = plus (minus level boundary) m } in IdxV i })
  ; goAtom level atom = case atom of 
      { VarA named -> case named of { Named name var -> case var of
        { IdxV idx   -> VarA (Named name (goVar level idx)) 
        ; TopV top   -> VarA (Named name (TopV top)) }}
      ; ConA named -> ConA named
      ; KstA lit   -> KstA lit   }
  ; go level term = case term of
    { AtmT named    -> sreturn (AtmF (goAtom level named))
    ; AppT t1 a2    -> sliftA2 AppF (go level t1) (sreturn (goAtom level a2))
    ; PriT pri args -> sreturn (PriF pri  ( map  (goAtom level) args))
    ; LZPT pri args -> sfmap   (LZPF pri) (smapM (go     level) args)
    ; LamT tm       -> sfmap LamF (termToClosure nstatic (prefixed "lambda") (inc level) (forgetName tm))
--    ; LamT _        -> case recogLamsT term of { Pair args body ->
--             sfmap LamF (lambdaToClosure "lambda" level (LambdaT (length args) body)) }
    ; CasT v brs    -> sfmap (CasF (goAtom level v)) (smapM (goBranch level) brs)
    ; RecT n nts tm -> let { level' = plus level n }
                       in  sliftA2 (RecF n) (smapM (goRec1 level') nts) (go level' tm) 
    ; LetT tm body  -> sliftA2 LetF (termToClosure nstatic (prefixed "let") level tm) (go (inc level) body) } 
  ; goRec1 level named = case named of { Named name tm -> sfmap (Named name) (termToStaticClosure nstatic (prefixed name) level tm) }
  ; goBranch level br  = case br of
    { DefaultT        rhs -> sfmap (DefaultF       ) (termToClosure    nstatic (prefixed "default")      level            rhs ) 
    ; BranchT named n rhs -> sfmap (BranchF named n) (lambdaToClosure nstatic  (prefixed (nameOf named)) level (LambdaT n rhs))
                                                -- (termToClosure nstatic (prefixed (nameOf named)) (plus level n) rhs)
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
makeDataConTable trie = ssequence_
  [ addLines [ "char *datacon_table[] = " ]
  , sforM_ (zipFirstRest ("  { ") ("  , ") list) (\pair -> 
      case pair of { Pair prefix pair2 -> case pair2 of { Pair idx name ->
        addWords [ prefix , doubleQuoteString name , "   // " , showInt idx ] }})
  , addLines [ "  };" ] ]
  where 
    list = mapFromList (map swap (trieToList trie))

liftedProgramToCode :: DataConTable -> LiftedProgram -> CodeGenM_
liftedProgramToCode dcontable pair = case pair of { LProgram toplevs topidxs main -> 
  let { ntoplevs = length toplevs ; nfo = StatInfo topidxs } in ssequence_
    [ addLines [ "" , concat [ "#include " , doubleQuoteString "rts.c" ] ]
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , makeDataConTable dcontable
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , smapM_ (toplevToCode nfo) toplevs
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , makeStaticFunctionTables toplevs
    , addLines [ "" , "// ----------------------------------------" , "" ]
    , addLines [ "int main(int argc, char **argv) {"
               , "StaticFunPointers = static_funptr_table;"
               , "StaticFunArities  = static_arity_table;" 
               , "ConstructorNames  = datacon_table;" ]
    , addWords [ "NStatic           = ", showInt ntoplevs , " ;   // number of static functions " ]
    , addLines [ "rts_initialize(argc,argv);" , "// main " ]
    , sbind (liftedToCode nfo main) (\result -> sseq
        (addWords [ "// printf(" , doubleQuoteStringLn "done." , ");" ])
        (addWords [ "rts_generic_println(" , result , ");" ]))
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
--    , debugInfoToCode name statfun
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
  ; TopV j -> case nfo of { StatInfo idxlist ->
                concat [ "(heap_ptr) static_stack[" , showInt (index j idxlist) , "]" ] }}

-- forces thunks
loadVar ::  StatInfo -> Var -> CodeLine
loadVar nfo var = case var of
  { IdxV i -> concat [ "rts_force_thunk_at( SP - " , showInt (inc i) , ")" ]
  ; TopV j -> case nfo of { StatInfo idxlist ->
                concat [ "rts_force_thunk_at( static_stack + " , showInt (index j idxlist) , ")" ] }}

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
  Or   -> binary  args (\arg1 arg2 -> withFreshVar "res_or"    (\fres -> 
            sbind (addWords [ "heap_ptr " , fres , ";" ])      (\_    -> 
            sbind (liftedToCode nfo arg1)                      (\res1 -> 
            sbind (addWords [ "if TO_BOOL(" , res1 , ") { " , fres , " = " , res1 , "; } else { " ]) (\_ -> 
            sbind (liftedToCode nfo arg2)                      (\res2 -> 
            sbind (addWords [ fres , " = " , res2 , "; } "])   (\_ -> sreturn fres)))))))
  And  -> binary  args (\arg1 arg2 -> withFreshVar "res_and"   (\fres -> 
            sbind (addWords [ "heap_ptr " , fres , ";" ])      (\_    -> 
            sbind (liftedToCode nfo arg1)                      (\res1 -> 
            sbind (addWords [ "if TO_BOOL(" , res1 , ") { " ]) (\_    -> 
            sbind (liftedToCode nfo arg2)                      (\res2 -> 
            sbind (addWords [ fres , " = " , res2 , "; } else { " , fres , " = " , res1 , "; } "])  (\_ -> sreturn fres)))))))
  IFTE -> ternary args (\barg arg1 arg2 -> withFreshVar "res_if"    (\fres ->
            sbind (addWords [ "heap_ptr " , fres , ";" ])           (\_    -> 
            sbind (liftedToCode nfo barg)                           (\bres -> 
            sbind (addWords [ "if TO_BOOL(" , bres , ") { " ])      (\_    -> 
            sbind (liftedToCode nfo arg1)                           (\res1 -> 
            sbind (addWords [ fres , " = " , res1 , "; } else { "]) (\_    -> 
            sbind (liftedToCode nfo arg2)                           (\res2 -> 
            sbind (addWords [ fres , " = " , res2 , "; }" ])        (\_ -> sreturn fres)))))))))
  _    -> error "unimplemented lazy primop"

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
--        ClosureF static env arity -> let { i = minus n (inc j) } in swhen (eq arity 0) (withFreshVar "val" (\val -> sseq
--          (addWords [ "heap_ptr " , val , " = rts_force_value( (heap_ptr) " , pre_sp, "[", showInt j , "] );" ])
--          (addWords [ pre_sp, "[", showInt j , "] = (uint64_t) " , val , " ;" ]) )) }})
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
    , addWords [ "SP = " , oldsp , " ;   // branches allocate ?! " ]
    , addLine    "}"
    ]) (\_ -> sreturn result )))))
  where 
    { worker result scrutinee branch = case branch of
        { DefaultF closure -> ssequence_
            [ addLine "default: {" 
            , sbind (closureToCode nfo closure) (\res -> addSetValue result res) 
            , addLine "break; }" ]
        ; BranchF namedcon arity closure -> case namedcon of { Named cname con -> withFreshVar2 "env" "args" (\envptr args -> 
            case closure of { ClosureF cbody env arity -> ssequence_
              [ addWords [ "case HTAG_DATACON(" , showInt con , "," , showInt arity , "): {    // " , cname , "/" , showInt arity ]
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

--         ; BranchF namedcon arity closure -> case namedcon of { Named cname con -> sbind (freshVar "args") (\args -> ssequence_
--             [ addWords [ "case HTAG_DATACON(" , showInt con , "," , showInt arity , "): {    // " , cname , "/" , showInt arity ]
--             , swhen (gt arity 0) (ssequence_
--                 [ addWords [ "stack_ptr " , args , " = rts_stack_allocate(" , showInt arity , ");" ]
--                 , sforM_ (range arity) (\j -> addWords [ args , "[" , showInt j , "] = " , scrutinee , "[" , showInt (inc j) , "];" ])
--                 ])
--             , let { clargs = map IdxV (reverse (range arity)) } 
--               in  sbind (applyClosure nfo closure clargs) (\res -> addSetValue result res) 
--             , addLine "break; }" ] ) }}}

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
  ; _ -> sbind (evalToReg nfo "fun" fun) (\funvar -> genericApplicationTo nfo funvar args) }}

--------------------------------------------------------------------------------
