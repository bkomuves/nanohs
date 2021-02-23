
-- | The idea is to write a self-hosting compiler (and interpreter) in
-- a very small subset of Haskell (basically untyped lambda calculus +
-- constructors; but with Haskell-compatible syntax, so that the same
-- program can be also executed by GHC):
--
-- * no static type system (untyped lambda calculus)
-- * na data type declarations (constructors are arbitrary capitalized names)
-- * no modules (single file)
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

{-# LANGUAGE NoImplicitPrelude  #-}
{- LANGUAGE Strict -}
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

-- had to move this into the 'PrimGHC' module
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

--------------------------------------------------------------------------------
-- ** Bool

-- Had to move this into the 'PrimGHC' module
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

data Triple a b c = Triple a b c deriving Show

fst3 :: Triple a b c -> a
fst3 triple = case triple of { Triple x _ _ -> x }

snd3 :: Triple a b c -> b
snd3 triple = case triple of { Triple _ y _ -> y }

thd3 :: Triple a b c -> c
thd3 triple = case triple of { Triple _ _ z -> z }

--------------------------------------------------------------------------------
-- ** Lists

-- had to move this into the 'PrimGHC' module
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

--------------------------------------------------------------------------------
-- ** Strings

-- had to move this into the 'PrimGHC' module
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

doubleQuoteString :: String -> String
doubleQuoteString = delimString doubleQuoteC doubleQuoteC

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
unlines :: List String -> String
unwords = intercalate (Cons ' '      Nil)
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
identifierL = pbind _alphaL                                     (\x  ->
              pbind (many (alternative alphaNumL (oneOf "_'"))) (\xs ->
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

data Defin = Defin Name Expr deriving Show

definedName :: Defin -> Name
definedName defin = case defin of { Defin n _ -> n }

definedExpr :: Defin -> Expr
definedExpr defin = case defin of { Defin _ e -> e }

type Program = List Defin

-- | We \"parse\" (well, recognize) type declarations, data declarations,
-- type synonyms and imports, but we ignore them; this is simply so that the
-- this source code can be a valid Haskell program and self-hosting at the
-- same time.
data TopLevel
  = TopDefin    Defin
  | TopTyDecl   Name (List Token)
  | TopDataDecl (List Token)
  | TopTyAlias  (List Token)
  | TopImport   (List Token)
  | TopModule   (List Token)
  deriving Show

mbDefin :: TopLevel -> Maybe Defin
mbDefin toplev = case toplev of { TopDefin def -> Just def ; _ -> Nothing }

programToExpr :: Program -> Expr
programToExpr defs = LetE defs (VarE "main")

data Expr
  = VarE  Name
  | AppE  Expr Expr
  | LamE  Name Expr
  | LetE  (List Defin) Expr
  | CaseE Expr (List BranchE)
  | LitE  Literal
  | ListE (List Expr)
  | PrimE PrimOp (List Expr)
  deriving Show

data BranchE
  = BranchE Name (List Name) Expr
  | DefaultE Expr
  deriving Show

lamsE :: List Name -> Expr -> Expr
lamsE args body = case args of { Nil -> body ; Cons v vs -> LamE v (lamsE vs body) }

appsE :: Expr -> List Expr -> Expr
appsE fun  args = case args of { Nil -> fun  ; Cons t ts -> appsE (AppE fun t) ts  }

listAppsE :: List Expr -> Expr
listAppsE  list = case list of { Cons f args -> appsE f args ; Nil -> error "listAppsE" }

--------------------------------------------------------------------------------
-- ** Primops

data Prim
  = Negate | Plus | Minus | Times | Div | Mod | Chr | Ord
  | IFTE | Not | And | Or | GenEQ | IntEQ | IntLT | IntLE
  | GetChar | PutChar | GetArg | Exit | Error 
  deriving (Eq,Show)

showPrim :: Prim -> String
showPrim prim = case prim of
  { Negate  -> "Negate"  ; Plus    -> "Plus"    ; Minus   -> "Minus"
  ; Times   -> "Plus"    ; Div     -> "Minus"   ; Mod     -> "Mod"
  ; Chr     -> "Chr"     ; Ord     -> "Ord"     ; IFTE    -> "IFTE"
  ; Not     -> "Not"     ; And     -> "And"     ; Or      -> "Or"
  ; IntEQ   -> "IntEQ"   ; IntLT   -> "IntLT"   ; IntLE   -> "IntLE"
  ; GenEQ   -> "GenEQ"   ; Error   -> "Error"   ; Exit    -> "Exit" 
  ; GetChar -> "GetChar" ; PutChar -> "PutChar" ; GetArg  -> "GetArg" }

type Arity = Int

data PrimOp = PrimOp Arity Prim deriving Show

primops :: Trie PrimOp
primops = trieFromList
  [ Pair "error"   (PrimOp 1  Error  )
  , Pair "negate"  (PrimOp 1  Negate )
  , Pair "plus"    (PrimOp 2  Plus   )
  , Pair "minus"   (PrimOp 2  Minus  )
  , Pair "times"   (PrimOp 2  Times  )
  , Pair "div"     (PrimOp 2  Div    )
  , Pair "mod"     (PrimOp 2  Mod    )
  , Pair "chr"     (PrimOp 1  Chr    )
  , Pair "ord"     (PrimOp 1  Ord    )
  , Pair "ifte"    (PrimOp 3  IFTE   )
  , Pair "not"     (PrimOp 1  Not    )
  , Pair "and"     (PrimOp 2  And    )
  , Pair "or"      (PrimOp 2  Or     )
  , Pair "geq"     (PrimOp 2  GenEQ  )
  , Pair "eq"      (PrimOp 2  IntEQ  )
  , Pair "lt"      (PrimOp 2  IntLT  )
  , Pair "le"      (PrimOp 2  IntLE  )
  , Pair "getChar" (PrimOp 1  GetChar)
  , Pair "putChar" (PrimOp 1  PutChar)
  , Pair "getArg"  (PrimOp 1  GetArg )
  , Pair "exit"    (PrimOp 1  Exit   )
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
recogPrimApps :: Expr -> Expr
recogPrimApps = go where
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
keywords = [ "where" , "case" , "of" , "let" , "in" , "module" , "import" , "data" , "type" ]

isKeyword :: String -> Bool
isKeyword str = elem str keywords

topLevelP :: Parse TopLevel
topLevelP = choice
  [ tyAliasP
  , dataDeclP
  , importP
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

importP :: Parse TopLevel
importP = pbind (keywordP "import") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopImport toks) ))

moduleP :: Parse TopLevel
moduleP = pbind (keywordP "module") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopModule toks) ))

definP :: Parse Defin
definP = pbind varP              (\name ->
         pbind (many varP)       (\args ->
         pbind (specP EqualSign) (\_    ->
         pbind exprP             (\body -> preturn (Defin name (lamsE args body)) ))))

exprP :: Parse Expr
exprP = pbind nakedExprP             (\expr ->
        pbind (optional whereBlockP) (\mb   ->
        preturn (case mb of { Nothing -> expr ; Just defs -> LetE defs expr } )))

whereBlockP :: Parse (List Defin)
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
atomP e = choice
  [ inParensP exprP
  , pfmap LitE  literalP
  , pfmap ListE listExprP
  , caseExprP
  , letExprP
  , pfmap VarE varP
  ] e

specP :: Special -> Parse Special
specP spec = preplace spec (token (SpecTok spec))

literalP :: Parse Literal
literalP = accept mbLit

identP :: Parse Name
identP = accept mbVar

-- | This does not accepts they keywords
varP :: Parse Name
varP = pbind identP (\v -> ifte (isKeyword v) pfail (preturn v))

keywordP :: String -> Parse String
keywordP word = pbind identP (\v -> ifte (geq v word) (preturn word) pfail)

inParensP :: Parse a -> Parse a
inParensP p = pbind (specP LParen) (\_ ->
              pbind p              (\x ->
              pbind (specP RParen) (\_ -> preturn x)))

listExprP  :: Parse (List Expr   )
tupleExprP :: Parse (List Expr   )
blockP     :: Parse (List Defin  )
branchesP  :: Parse (List BranchE)

listExprP  = pbind (specP LBracket) (\_ -> sepEndBy (specP Comma    ) (specP RBracket) exprP  )
tupleExprP = pbind (specP LParen  ) (\_ -> sepEndBy (specP Comma    ) (specP RParen  ) exprP  )
blockP     = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) definP )
branchesP  = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) branchP)

branchP :: Parse BranchE
branchP = alternative defaultBranchP branchP'

branchP' :: Parse BranchE
branchP' = pbind varP          (\con  ->
           pbind (many varP  ) (\args ->
           pbind (specP Arrow) (\_    ->
           pbind (exprP      ) (\body -> preturn (BranchE con args body)))))

defaultBranchP :: Parse BranchE
defaultBranchP = pbind (keywordP "_") (\_  ->
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

forgetName :: Named a -> a
forgetName x = case x of { Named _ y -> y }

nameOf :: Named a -> String
nameOf x = case x of { Named n _ -> n }

data Term
  = VarT (Named Idx )
  | ConT (Named Con )
  | LamT (Named Term)
  | AppT Term Term
  | PriT PrimOp (List Term)
  | RecT Int (List (Named Term)) Term
  | CasT Idx (List BranchT)
  | KstT Literal
  deriving Show

data BranchT
  = BranchT (Named Con) Int Term
  | DefaultT Term
  deriving Show

exprToCore :: Expr -> Term
exprToCore expr = scopeCheck (collectDataCons expr) trieEmpty (recogPrimApps expr)

programToCore :: Program -> Term
programToCore = compose exprToCore programToExpr

--------------------------------------------------------------------------------
-- ** Data constructors

isDCon :: Name -> Bool
isDCon name = isUpper (head name)

-- | Mapping constructor names to constructor tags
type DataConTable = Trie Con

conFalse   = 0
conTrue    = 1
conUnit    = 2
conNil     = 3
conCons    = 4
conNothing = 5
conJust    = 6

predefinedDataCons :: List (Pair String Int)
predefinedDataCons =
  [ Pair "False" conFalse , Pair "True" conTrue , Pair "Unit"    conUnit
  , Pair "Nil"   conNil   , Pair "Cons" conCons , Pair "Nothing" conNothing , Pair "Just" conJust ]

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
-- *  10.. = user defined constructors
--
-- We need to fix Int, Char, False, True, Unit, Nil, Cons, Just and Nothing
-- because the primops use them
--
collectDataCons :: Expr -> DataConTable
collectDataCons expr = snd (execState (go expr) (Pair 10 initial)) where
  { initial = trieFromList predefinedDataCons
  ; insert name = sbind sget (\pair -> case pair of { Pair n table -> case trieLookup name table of
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

type Scope = Trie Level

lookupVar :: Level -> Scope -> String -> Idx
lookupVar level scope name =
  case trieLookup name scope of { Just k -> dec (minus level k) ; Nothing ->
    error (append3 "variable name " (quoteString name) " not in scope") }

lookupCon :: DataConTable -> String -> Con
lookupCon dcontable name =
  case trieLookup name dcontable of { Just con -> con ; Nothing ->
    error (append3 "fatal error: constructor" (quoteString name) " not found") }

scopeCheck :: DataConTable -> Scope -> Expr -> Term
scopeCheck dcontable = go 0 where
  { go level scope expr = case expr of
    { VarE  name -> case isDCon name of
        { True  -> ConT (Named name (lookupCon dcontable   name))
        ; False -> VarT (Named name (lookupVar level scope name)) }
    ; AppE  e1 e2 -> AppT (go level scope e1) (go level scope e2)
    ; LamE  name body -> LamT (Named name (go (inc level) (trieInsert name level scope) body))
    ; LetE  defs body -> let { n = length defs ; level' = plus level n
        ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name j scp }
        ; scope' = foldl f scope (zip (map definedName defs) (rangeFrom level n))
        } in RecT n (map (goDefin level' scope') defs) (go level' scope' body)
    ; CaseE what brs -> case what of
        { VarE name -> goCase level scope (lookupVar level scope name) brs
        ; _         -> RecT 1 (singleton (Named "$0" (go (inc level) scope what))) (goCase (inc level) scope 0 brs) }
    ; LitE  lit -> case lit of
        { StrL cs -> go level scope (ListE (map (\x -> LitE (ChrL x)) cs))
        ; _       -> KstT lit }
    ; ListE exprs -> case exprs of { Nil -> ConT (Named "Nil" conNil)
        ; Cons e es -> AppT (AppT (ConT (Named "Cons" conCons)) (go level scope e)) (go level scope (ListE es)) }
    ; PrimE prim args -> PriT prim (map (go level scope) args)
    }
  ; goDefin level scope defin = case defin of { Defin name what -> Named name (go level scope what) }
  ; goCase level scope idx branches = CasT idx (map goBranch branches) where
    { goBranch branch = case branch of
        { DefaultE         rhs -> DefaultT (go level scope rhs)
        ; BranchE con args rhs -> let { n = length args ; level' = plus level n
          ; f scp nameidx = case nameidx of { Pair name j -> trieInsert name j scp }
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

-- | Force thunks
forceValue :: Value -> Value
forceValue val = case val of { ThkV env tm -> eval env tm ; _ -> val }

showValue :: Value -> String
showValue value = case value of
  { IntV n -> showInt n
  ; ChrV c -> quoteChar c
  ; ConV con args -> let { tag = append "Con#" (showInt con) } in case args of { Nil -> tag
    ; Cons _ _ -> parenString (unwords (Cons tag (map showValue args))) }
  ; LamV   _ -> "<lambda>"
  ; ThkV env tm -> showValue (eval env tm)
  }

eqValue :: Value -> Value -> Bool
eqValue val1 val2 = case val1 of
  { IntV i1 -> case val2 of { IntV i2 ->  eq i1 i2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
  ; ChrV c1 -> case val2 of { ChrV c2 -> ceq c1 c2 ; ThkV e2 t2 -> eqValue val1 (eval e2 t2) ; _ -> False }
  ; ConV con1 args1 -> case val2 of
      { ConV con2 args2 -> and3 (eq con1 con2) (eq (length args1) (length args2))
                                (andList (zipWith eqValue args1 args2))
      ; ThkV env2 tm2   -> eqValue val1 (eval env2 tm2)
      ; _ -> False }
  ; LamV _        -> False
  ; ThkV env1 tm1 -> eqValue (eval env1 tm1) val2
  }

boolToValue :: Bool -> Value
boolToValue b = ifte b (ConV conTrue Nil) (ConV conFalse Nil)

valueToBool :: Value -> Bool
valueToBool val = case val of { ConV con args -> eq con conTrue ; _ -> error "not a boolean" }

intToValue :: Int -> Value
intToValue = IntV

valueToInt :: Value -> Int
valueToInt val = case val of { IntV x -> x ; _ -> error "not an integer" }

charToValue :: Char -> Value
charToValue = ChrV

maybeCharToValue :: Maybe Char -> Value
maybeCharToValue mb = case mb of { Nothing -> ConV conNothing Nil ; Just c -> ConV conJust (singleton (ChrV c)) }

valueToChar :: Value -> Char
valueToChar val = case val of { ChrV c -> c ; _ -> error "not a character" }

unitToValue :: Unit -> Value
unitToValue Unit = ConV conUnit Nil

valueToUnit :: Value -> Unit
valueToUnit val = case val of { ConV con _ -> ifte (eq con conUnit) Unit err ; _ -> err } where
  { err = error "not a unit" }

listToValue :: List Value -> Value
listToValue list = case list of { Nil -> ConV conNil Nil
  ; Cons x xs -> ConV conCons [ x , listToValue xs ] }

valueToList :: Value -> List Value
valueToList value = case value of
  { ConV con args -> ifte (neq con conCons) Nil
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
  ; IFTE    -> error "ifte: this has to be implemented somewhere else because of lazyness"
  ; Not     -> unary   args (evalfunBB  not )
  ; And     -> binary  args (evalfunBBB and )
  ; Or      -> binary  args (evalfunBBB or  )
  ; GenEQ   -> binary  args (\x y -> boolToValue (eqValue x y))
  ; IntEQ   -> binary  args (evalfunIIB eq  )
  ; IntLT   -> binary  args (evalfunIIB lt  )
  ; IntLE   -> binary  args (evalfunIIB le  )
  ; GetChar -> unary   args (compose3 maybeCharToValue getChar valueToUnit)
  ; PutChar -> unary   args (compose3 unitToValue      putChar valueToChar)
  ; Exit    -> unary   args (compose3 unitToValue      exit    valueToInt )
--  ; GetArg  -> ??? where should the interpreter get the arguments ???
--  ; IsEOF   -> unary   args (compose3 boolToValue isEOF   valueToUnit)
  ; _       -> error "evalPrim: unimplemented primop"
  }

--------------------------------------------------------------------------------
-- ** The evaluator

-- in reverse order as usual
type Env = List Value

eval :: Env -> Term -> Value
eval env term = case term of
  { VarT idx     -> forceValue (index (forgetName idx) env)
  ; ConT con     -> ConV (forgetName con) Nil
  ; AppT e1 e2   -> case eval env e1 of
    { LamV fun      -> fun (eval env e2)
    ; ConV con args -> ConV con (snoc args (eval env e2))
    ; _             -> error "application to non-lambda (int/char)"
    }
  ; PriT primop ts -> case primop of { PrimOp _arity prim -> case prim of
    { IFTE -> ternary ts (lazyIFTE env)
    ; And  -> binary  ts (lazyAnd  env)
    ; Or   -> binary  ts (lazyOr   env)
    ; _    -> evalPrim prim (map (eval env) ts) }}
  ; LamT body    -> LamV (\x -> eval (Cons x env) (forgetName body))
  ; CasT var brs -> case forceValue (index var env) of
    { ConV con args -> matchCon env con args brs
    ; _             -> error "branching on a non-constructor (lambda)"
    }
  ; RecT n ls tm -> let { env' = append (reverse (map (mkThunk env') ls)) env } in eval env' tm
  ; KstT lit     -> case lit of
    { IntL k       -> IntV k
    ; ChrL c       -> ChrV c
    ; StrL _       -> error "string literals should not appear in core"
    }
  }
  where { mkThunk env1 named = case named of { Named name body -> ThkV env1 body } }

lazyIFTE :: Env -> Term -> Term -> Term -> Value
lazyIFTE env tb tx ty = let { vb = eval env tb } in ifte (valueToBool vb) (eval env tx) (eval env ty)

lazyAnd :: Env -> Term -> Term -> Value
lazyAnd env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (eval env t2) (boolToValue False)

lazyOr :: Env -> Term -> Term -> Value
lazyOr env t1 t2 = let { v1 = eval env t1 } in ifte (valueToBool v1) (boolToValue True) (eval env t2)

matchCon :: Env -> Con -> List Value -> List BranchT -> Value
matchCon env con args = go where
  { nargs = length args
  ; go branches = case branches of
    { Nil -> error "non-exhaustive patterns in case"
    ; Cons this rest -> case this of
      { DefaultT rhs            -> eval env rhs
      ; BranchT bcon bnargs rhs -> ifte (and (eq con (forgetName bcon)) (eq nargs bnargs))
          (eval (append (reverse args) env) rhs)
          (go rest) } } }

--------------------------------------------------------------------------------
-- * The compiler
-- ** Closure conversion

-- | Index of statically known functions (and thunks); starts from zero
type Static = Int

-- | Variables can be a de Bruijn index, or a top-level definition
-- (the latter is only an optimization, so we don't have to allocate
-- closures for static functions)
data VarF
  = IdxF Idx
  | TopF Static
  deriving Show

prettyVarF :: VarF -> String
prettyVarF var = case var of 
  { IdxF i -> concat [  "de Bruijn (" , showInt i , ")" ] 
  ; TopF j -> concat [ "static fun (" , showInt j , ")" ] }

-- | We lift all lambdas (and lets, and branch right hand sides) to top-level
data Lifted
  = VarF (Named VarF)
  | ConF (Named Con )
  | KstF Literal
  | AppF Lifted Lifted
  | PriF PrimOp (List Lifted)
  | CasF VarF (List BranchF)
  | LamF ClosureF
  | RecF Int (List (Named ClosureF)) Lifted
  deriving Show

data BranchF
  = BranchF (Named Con) Int ClosureF
  | DefaultF ClosureF
  deriving Show

-- | When allocating a closure, we create a new local environment
-- by pruning the current environment. We also remember the number
-- of lambda arguments (0 = thunk)
data ClosureF = ClosureF Static (List Idx) Arity deriving Show

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

recogAppsF :: Lifted -> Pair Lifted (List Lifted)
recogAppsF term = case term of
  { AppF tm1 tm2 -> case recogAppsF tm1 of { Pair f args -> Pair f (snoc args tm2) }
  ; _            -> Pair term Nil }

-- | Figure out the part of the environment used by a term.
-- Returns a set of /levels/
pruneEnvironment :: Level -> Level -> Term -> IntSet
pruneEnvironment boundary = go where
  { go level term = case term of
    { VarT named  -> case named of { Named name idx ->
        let { j = minus level (inc idx) }
        in  ifte (lt j boundary) (setSingleton j) setEmpty }
    ; AppT t1 t2  -> setUnion (go level t1) (go level t2)
    ; PriT _ args -> setUnions (map (go level) args)
    ; LamT nbody  -> go (inc level) (forgetName nbody)
    ; RecT n ts t -> let { level' = plus level n }
                     in  setUnions (Cons (go level' t) (map (\t -> go level' (forgetName t)) ts))
    ; CasT _ brs  -> setUnions (map (goBranch level) brs)
    ; ConT _      -> setEmpty
    ; KstT _      -> setEmpty }
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
lambdaToClosure :: Name -> Level -> LambdaT -> ClosM ClosureF
lambdaToClosure name level lambda = case lambda of { LambdaT nargs body ->
  let { pruned   = pruneEnvironment level (plus level nargs) body
      ; npruned  = length pruned
      ; envtable = zip pruned (reverse (map negate (range npruned)))
      ; pr_idxs  = map (\j -> minus level (inc j)) pruned
      }
  in  sbind (closureConvert level envtable (plus level nargs) body) (\statbody ->
      sbind (addStatFun name (StatFun npruned nargs statbody))      (\statidx  ->
      sreturn (ClosureF statidx pr_idxs nargs))) }

coreToLifted :: Term -> Pair (List TopLev) Lifted
coreToLifted term = case runState (closureConvert 0 Nil 0 term) Nil of
  { Pair list main -> Pair (reverse list) main }

closureConvert :: Level -> ClosEnv -> Level -> Term -> State (List TopLev) Lifted
closureConvert boundary closEnv = go where
  { go level term = case term of
    { VarT named    -> sreturn (VarF (case named of { Named name idx ->
        let { j = minus level (inc idx) }
        in  ifte (ge j boundary) (Named name (IdxF idx))
              (case mapLookup j closEnv of
                { Nothing -> error "closureConvert: fatal error: variable not in the pruned environment"
                ; Just m  -> let { i = plus (minus level boundary) m }
                             in  Named name (IdxF i)
                }) }))
    ; ConT named    -> sreturn (ConF named)
    ; KstT lit      -> sreturn (KstF lit  )
    ; AppT t1 t2    -> sliftA2 AppF (go level t1) (go level t2)
    ; PriT pri args -> sfmap (PriF pri) (smapM (go level) args)
    ; LamT _        -> case recogLamsT term of { Pair args body ->
             sfmap LamF (lambdaToClosure "lambda" level (LambdaT (length args) body)) }
    ; CasT i brs    -> sfmap (CasF (IdxF i)) (smapM (goBranch level) brs)
    ; RecT n nts tm -> let { level' = plus level n }
                       in  sliftA2 (RecF n) (smapM (goRec1 level') nts) (go level' tm) }
  ; goRec1 level named = case named of { Named name tm -> case recogLamsT tm of
      { Pair args body -> sfmap (Named name) (lambdaToClosure name level (LambdaT (length args) body)) }}
  ; goBranch level br  = case br of
    { BranchT named n rhs -> sfmap (BranchF named n) (lambdaToClosure (nameOf named) level (LambdaT n rhs))
    ; DefaultT        rhs -> sfmap (DefaultF       ) (lambdaToClosure "default"      level (LambdaT 0 rhs))
    }}

--------------------------------------------------------------------------------
-- * C language code generation
-- ** Scaffoldings

type CodeLine = String

staticLabel :: Static -> String
staticLabel fun = append ("static_") (showInt fun) 

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
      [ addLines [ "" , "int static_arity_table[] = " ]
      , sforM_ (zipFirstRest ("  { ") ("  , ") toplevs) (\pair -> case pair of { Pair prefix toplev ->
          case toplev of { TopLev named statfun -> case named of { Named name static ->
            case statfun of { StatFun envsize arity lifted ->
              addWords [ prefix , showInt envsize , " + " , showInt arity ] }}}})
      , addLines [ "  };"  ] ]
  }

programToCode :: Pair (List TopLev) Lifted -> CodeGenM_
programToCode pair = case pair of { Pair toplevs main -> ssequence_
  [ addLines [ "" , concat [ "#include " , doubleQuoteString "rts.c" ] , "" ]
  , smapM_ toplevToCode toplevs
  , addLines [ "" , "// ----------------------------------------" , "" ]
  , makeStaticFunctionTables toplevs
  , addLines [ "" , "// ----------------------------------------" , "" ]
  , addLines [ "int main() {"
             , "rts_initialize();"
             , "StaticFunPointers = &static_funptr_table;"
             , "StaticFunArities  = &static_arity_table;" ]
  , sbind (liftedToCode main) (\result -> addWords [ "rts_generic_print(" , result , ");" ])
  , addLines [ "exit(0);" , "}" ]
  ] }

toplevToCode :: TopLev -> CodeGenM_
toplevToCode toplev = case toplev of { TopLev named statfun -> case named of { Named name static ->
  case statfun of { StatFun envsize arity lifted -> let { ntotal = plus envsize arity } in ssequence_
    [ addLine ""
    , addWords [ "// static function `" , name , "` with arity = " , showInt envsize , " + " , showInt arity ]
    , addWords [ "heap_ptr " , staticLabel static , "() {" ]
    , addLine    "stack_ptr old_stackptr = Stack_ptr; "
    , sbind (liftedToCode lifted) (\result -> withFreshVar "final" (\fresult -> ssequence_
        [ addDefin fresult result
        , addLine    "Stack_ptr = old_stackptr; " 
        , addWords [ "return (" , fresult , ");" ] ] ))
    , addLine "}" ] }}}

--------------------------------------------------------------------------------
-- ** main code generation

-- -- | Allocate closure - arguments 
-- closureToCodeWith :: ClosureF -> [Name] -> CodeGenM CodeLine
-- closureToCodeWith closure = case closure of { ClosureF static env arity -> case env of

-- | Allocate closure - arguments come from the stack
closureToCode :: ClosureF -> CodeGenM CodeLine
closureToCode closure = case closure of { ClosureF static env arity -> case env of
  { Nil -> sreturn (concat [ "FROM_STATIDX(" , showInt static , ")" ])
  ; _   -> let { envsize = length env } in withFreshVar "closure_" (\var -> sseq3
    (addWords [ "heap_ptr " , var , " = rts_allocate_closure(" , staticLabel static , "," , showInt envsize , "," , showInt arity , ");" ])
    (addWords [ "for (int i=0;i<", showInt envsize , ";i++) " , var , "[i+2] = DE_BRUIJN(" , showInt (dec envsize) , "-i)"])
    (sreturn var)) }}

loadVarF ::  VarF -> CodeLine
loadVarF var = case var of
  { IdxF i -> concat [    "DE_BRUIJN(" , showInt i , ")" ]
  ; TopF j -> concat [ "FROM_STATIDX(" , showInt j , ")" ] }

liftedToCode :: Lifted -> CodeGenM CodeLine
liftedToCode lifted = case lifted of
  { VarF named -> case named of { Named name var -> sreturn (loadVarF var) }
  ; ConF named -> case named of { Named name con -> sreturn (concat [ "NULLARY_CON(" , showInt con , ")" ]) }
  ; KstF lit -> case lit of
      { IntL k -> sreturn (concat [ "INT_LITERAL(" , showInt k       , ")" ])
      ; ChrL c -> sreturn (concat [ "CHR_LITERAL(" , showInt (ord c) , ")" ])
      ; _      -> error "codegen: unimplemented literal constant" }
  ; PriF primop args  -> case primop of { PrimOp arity prim -> 
      withFreshVars "a" arity (\vars -> sseq
        (sforM_ (zip vars args) (\pair -> case pair of
            { Pair var arg -> sbind (liftedToCode arg) (\result -> addDefin var result) }))
        (sreturn (concat [ "prim_" , showPrim prim , "(" , intercalate "," vars , ")" ])) )}
  ; CasF var branches -> caseOfToCode var branches
  ; LamF closure      -> closureToCode closure
  ; AppF _ _          -> case recogAppsF lifted of { Pair fun args -> applicationToCode fun args }
  ; RecF n closs body -> letrecToCode n (map forgetName closs) body
  }

letrecToCode :: Int -> List ClosureF -> Lifted -> CodeGenM Name
letrecToCode n cls_list body = withFreshVar3 "obj" "letrec" "stackptr" (\obj loc old_stackptr -> 
  sseq (ssequence_
    [ addWords [ "// letrec " , showInt n ]
    , addWords [ "stack_ptr " , old_stackptr , " = Stack_ptr;" ]
    , addWords [ "stack_ptr " , loc , " = rts_stack_allocate(" , showInt n , ");" ]
    , sforM_ (zipIndex cls_list) (\pair -> case pair of { Pair j cls -> case cls of { ClosureF static env arity -> 
        let { target = concat [ loc, "[", showInt j , "]" ] } in withFreshVar "tgt" (\tgt -> ssequence_ 
          [ addWords [ target , " = (uint64_t) rts_allocate_closure( " , staticLabel static , " , " , showInt (length env) , " , " , showInt arity , " );" ]
          , addWords [ "heap_ptr " , tgt , " = (heap_ptr) " , target , ";" ] 
          , copyEnvironmentTo tgt 2 env ] )}})
    , sforM_ (zipIndex cls_list) (\pair -> case pair of { Pair j cls -> case cls of
        { ClosureF static env arity -> let { i = minus n (inc j) } in swhen (eq arity 0) (withFreshVar "val" (\val -> sseq
            (addWords [ "heap_ptr val = rts_force_thunk( " , loc, "[", showInt j , "] );" ])
            (addWords [ loc, "[", showInt j , "] = (uint64_t) val;" ]) )) }})
    , sbind (evalToVar "body" body) (\res -> addDefin obj res)   
    , addWords [ "Stack_ptr = " , old_stackptr , ";" ]
    ]) (sreturn obj))

-- NB: heap constructor tag should be compatible with the nullary constructor tag
caseOfToCode :: VarF -> List BranchF -> CodeGenM Name
caseOfToCode var branches = 
  sbind (freshVar "tagword"  ) (\tagword   -> 
  sbind (freshVar "result"   ) (\result    -> 
  sbind (freshVar "scrutinee") (\scrutinee -> 
  sbind (ssequence_ 
    [ addWords [ "// case " , prettyVarF var , " of" ]
    , addWords [ "uint64_t " , tagword , ";" ]
    , addWords [ "heap_ptr " , result  , ";" ]
    , addWords [ "heap_ptr " , scrutinee , " = " , loadVarF var , ";" ]
    , addWords [ "if IS_HEAP_PTR(" , scrutinee, ") " , tagword , " = " , scrutinee , "[0]; else " , tagword , " = (intptr_t)" , scrutinee , " ;" ]
    , addWords [ "switch(" , tagword , ") {" ]
    , smapM_ (worker result scrutinee) branches
    , addLine    "}"
    ]) (\_ -> sreturn result ))))
  where 
    { worker result scrutinee branch = case branch of
        { DefaultF closure -> ssequence_
            [ addLine "default: {" 
            , sbind (closureToCode closure) (\res -> addSetValue result res) 
            , addLine "break; }" ]
        ; BranchF namedcon arity closure -> case namedcon of { Named cname con -> sbind (freshVar "args") (\args -> ssequence_
            [ addWords [ "case HTAG_DATACON(" , showInt con , "," , showInt arity , "): {    // " , cname , "/" , showInt arity ]
            , swhen (gt arity 0) (ssequence_
                [ addWords [ "stack_ptr " , args , " = rts_stack_allocate(" , showInt arity , ");" ]
                , sforM_ (range arity) (\j -> addWords [ args , "[" , showInt j , "] = " , scrutinee , "[" , showInt (inc j) , "]" ])
                ])
            , sbind (closureToCode closure) (\res -> addSetValue result res) 
            , addLine "break; }" ] ) }}}

--------------------------------------------------------------------------------
-- ** application

evalToVar :: String -> Lifted -> CodeGenM Name
evalToVar name term = withFreshVar name (\var -> sbind (liftedToCode term) (\res -> sseq
  (addWords [ "heap_ptr " , var , " = " , res , ";"]) (sreturn var)))

evalAndCopyArgs :: Name -> Int -> List Lifted -> CodeGenM_
evalAndCopyArgs target ofs args = sforM_ (zipIndex args) (\pair -> case pair of { Pair j tm ->
  sbind (liftedToCode tm) (\result -> addWords [ target , "[" , showInt (plus j ofs) , "] = " , result , " ;"] ) } )

evalAndPushArgs :: List Lifted -> CodeGenM Name
evalAndPushArgs args = withFreshVar "tmp" (\tmp -> sseq (ssequence_
  [ addWords [ "stack_ptr " , tmp , " =  rts_stack_allocate(" , showInt (length args) , ");" ]
  , evalAndCopyArgs tmp 0 args ]) (sreturn tmp))

copyEnvironmentTo :: Name -> Int -> List Idx -> CodeGenM_
copyEnvironmentTo target ofs env = sforM_ (zipIndex env) (\pair -> case pair of { Pair j idx -> 
  addWords [ target , "[" , showInt (plus j ofs) , "] = DE_BRUIJN(" , showInt idx , ");" ] } )

-- copy environment, evaluate args, and assemble these on the stack
assembleClosureArgs :: List Idx -> List Lifted -> CodeGenM Name
assembleClosureArgs env args = let { envsize = length env ; nargs = length args ; ntotal = plus envsize nargs } in 
  ifte (eq ntotal 0) (sreturn "NULL") 
  ( withFreshVar "tmp" (\tmp -> sseq (ssequence_
    [ addWords [ "stack_ptr " , tmp , " =  rts_stack_allocate(" , showInt ntotal , ");" ]
    , copyEnvironmentTo tmp 0       env
    , evalAndCopyArgs   tmp envsize args ]) (sreturn tmp)))

genericApplicationTo :: Name -> List Lifted -> CodeGenM Name
genericApplicationTo funvar args = let { nargs = length args } in 
  withFreshVar "fresult"       (\finalres -> 
  sbind (evalAndPushArgs args) (\tmp      ->
  sbind (addWords [ "heap_ptr " , finalres , " = rts_apply( " , funvar , " , " , showInt nargs , " , " , tmp , ");" ]) (\_ ->
  sbind (addWords [ "Stack_ptr = " , tmp , ";" ]) (\_ -> (sreturn finalres) ))))

callStatic :: Static -> CodeGenM Name
callStatic sidx= withFreshVar "result" (\var -> sseq
  (addWords [ "heap_ptr " , var , " = " , staticLabel sidx , "();" ])
  (sreturn var))

applicationToCode :: Lifted -> List Lifted -> CodeGenM CodeLine
applicationToCode fun args = let { nargs = length args } in case args of { Nil -> liftedToCode fun ; _ -> case fun of
  { LamF closure -> case closure of { ClosureF static env fun_arity -> 
      let { envsize = length env ; ntotal = plus envsize fun_arity } in case compare nargs fun_arity of
        { EQ -> sbind (assembleClosureArgs env args) (\tmp -> callStatic static)
        ; GT -> sbind (assembleClosureArgs env (take fun_arity args)) (\tmp    -> 
                sbind (callStatic static)                             (\funres -> 
                      (genericApplicationTo funres (drop fun_arity args))))
        ; LT -> withFreshVar "obj" (\obj -> sseq (ssequence_
                  [ addWords [ "heap_ptr ", obj , " = rts_allocate_closure( " , staticLabel static , " , " , showInt ntotal , " , " , showInt (minus fun_arity nargs) , " );" ]
                  , copyEnvironmentTo obj 2              env
                  , evalAndCopyArgs   obj (inc2 envsize) args 
                  ]) (sreturn obj)) } }
  ; ConF named -> case named of { Named dcon_name con -> withFreshVar "obj" (\obj -> sseq (ssequence_
      [ addWords [ "heap_ptr ", obj , " = rts_allocate_datacon( " , showInt con , "," , showInt nargs , ");   // " , dcon_name ]
      , evalAndCopyArgs  obj 1 args 
      ]) (sreturn obj)) }
  ; _ -> sbind (evalToVar "fun" fun) (\funvar -> genericApplicationTo funvar args) }}

--------------------------------------------------------------------------------
