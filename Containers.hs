-- | Containers

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists#-}

module Containers where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base

{-% include "Base.hs" %-}

--------------------------------------------------------------------------------
-- * Containers
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

-- | throws an exception if the key already exists
trieInsertNew :: String -> String -> a -> Trie a -> Trie a
trieInsertNew errmsg string y = go string where
  { go str trie = case trie of { Node mb table -> case str of
    { Nil -> case mb of { Nothing -> Node (Just y) table ; _ -> error errmsg }
    ; Cons x xs -> Node mb (mapInsert (ord x) (trieSingleton xs y) (go xs) table) } } }

trieDelete :: String -> Trie a -> Trie a
trieDelete str trie = case trie of { Node mb table -> case str of
  { Nil -> Node Nothing table
  ; Cons x xs -> Node mb (mapAdjust (ord x) (trieDelete xs) table) } }

trieFromList :: List (Pair String a) -> Trie a
trieFromList = foldr f trieEmpty where { f kv trie = case kv of { Pair k v -> trieInsert k v trie } }

-- | throws an exception if there is a duplicate key
trieFromListUnique :: (String -> String) -> List (Pair String a) -> Trie a
trieFromListUnique errmsg = foldr f trieEmpty where { f kv trie = case kv of { Pair k v -> trieInsertNew (errmsg k) k v trie } } 

trieToList :: Trie a -> List (Pair String a)
trieToList = go where { go trie = case trie of { Node mb table -> let
  { f pair = case pair of { Pair k trie' -> map (prepend (chr k)) (go trie') }
  ; rest = concat (map f table)
  ; prepend x pair = case pair of { Pair xs y -> Pair (Cons x xs) y } }
  in case mb of { Nothing -> rest ; Just y -> Cons (Pair Nil y) rest } } }

--------------------------------------------------------------------------------
