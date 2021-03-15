
{-# LANGUAGE Strict, FlexibleContexts, PatternSynonyms #-}
module TopSortSCC where

import Control.Monad
import Control.Monad.State.Strict

import qualified Data.Map.Strict as Map ; import Data.Map.Strict (Map)
import qualified Data.Set        as Set ; import Data.Set        (Set)

import Data.List
import System.Random

--------------------------------------------------------------------------------

ex = Map.fromList exlist

exlist =
  [ ( "a" , [ "a" , "b" ]            )
  , ( "b" , [ "c" , "d" , "e" , "j"] )
  , ( "c" , [ "c" ]                  )
  , ( "d" , []                       )
  , ( "e" , [ "d" ]                  )
  , ( "f" , [ "g" ]                  )
  , ( "g" , [ "h" , "i" ]            )
  , ( "h" , [ "f" , "j" ]            )
  , ( "i" , []                       )
  , ( "j" , [ "k" , "l" ]            )
  , ( "l" , [ "l" ]                  )
  , ( "k" , []                       )         
  ]

pattern Pair x y = (x,y)
ex2 = Map.fromList [Pair "foldl" [],Pair "main" ["foldl"],Pair "map" []]

--------------------------------------------------------------------------------

type Vtx   = String
type Graph = Map Vtx [Vtx]

graphToList :: Graph -> [(Vtx,Vtx)]
graphToList g = [ (v,w) | (v,ws) <- Map.toList g , w <- ws ]

graphFromList :: [(Vtx,Vtx)] -> Graph 
graphFromList = buildMap (:[]) (:) 

flipGraph :: Graph -> Graph
flipGraph graph = insertKeys $ graphFromList $ map swap $ graphToList graph where
  swap (x,y) = (y,x)
  keys = Map.keys graph
  insertKeys g = foldl (\old k -> Map.alter h k old) g keys
  h Nothing   = Just []
  h (Just ys) = Just ys

buildMap :: Ord k => (a -> b) -> (a -> b -> b) -> [(k,a)] -> Map k b
buildMap f g xys = foldl' insert Map.empty xys where
  insert old (k,x) = Map.alter (h x) k old
  -- h :: a -> Maybe b -> Maybe b
  h x Nothing  = Just (f x  )
  h x (Just y) = Just (g x y)

randomGraph :: Int -> Double -> IO Graph
randomGraph n threshold = 
  do
    zs <- replicateM n2 $ randomRIO (0,1)
    return $ graphFromList [ (f i, f j) | (z,(i,j)) <- zip zs edges , z < threshold ]
  where
    n2 = n*n
    edges = [ (i,j) | i<-[1..n], j<-[1..n] ]
    f i = "v" ++ show i

test = do
  forM_ [0.05,0.10..0.95] $ \threshold -> do
    putStrLn $ "threshold = " ++ show threshold
    graphs <- replicateM 25 (randomGraph 15 threshold) 
    print $ map checkSCC graphs

--------------------------------------------------------------------------------

checkSCC :: Graph -> Bool
checkSCC graph = case checkSCC' graph of
  (b1,b2s,b3s) -> {- b1 && -} (and b2s) && (and b3s)
  -- the vertex set is not really known

checkSCC' graph = ( checkSet , checkOrder , checkSC ) where

  scc = reverse $ tarjanSCC (flipGraph graph)

  lkpNeighs v = Map.findWithDefault [] v graph

  -- does the result covers the vertex set?
  checkSet = sort (concat scc) == Map.keys graph

  -- is it ordered (topologically sorted)?
  checkOrder = worker scc where
    worker []     = []
    worker [this] = []
    worker (this:rest) = thisOK : worker rest where
      thisOK = and [ w `elem` these | v <- this , w <- lkpNeighs v ] where
      these  = this ++ concat rest

  -- are the components really SCC-s (can you reach each vertex from each other vertex?)
  checkSC = (map isSCC scc)

  isSCC vtxset = 
    and [ w `elem` reachv | v <- vtxset , let reachv = Set.toList (reachableSet graph v) , w <- vtxset ]
  
reachableSet :: Graph -> Vtx -> Set Vtx
reachableSet graph vtx0 = execState (go vtx0) (Set.empty) where
  go :: Vtx -> State (Set Vtx) ()
  go v = do
    visited <- get 
    unless (Set.member v visited) $ do
      put (Set.insert v visited)
      let neighs = Map.findWithDefault [] v graph :: [Vtx] 
      mapM_ go neighs

--------------------------------------------------------------------------------
-- * Tarjan's topologically sorted SCC algorithm

data Tarjan = Tarjan 
  { _next   :: Int
  , _stack  :: [Vtx] 
  , _links  :: Map Vtx (Int,Int)   -- ^ index and low-linkg
  , _output :: [[Vtx]]
  }
  deriving Show

-- | Based on <https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm>
tarjanSCC :: Graph -> [[Vtx]]
tarjanSCC graph = _output (execState (mapM_ worker vtxSet) iniState) where

  iniState = Tarjan 0 [] Map.empty []

  vtxSet = Map.keys graph

  worker v = do
    get >>= \state -> case Map.lookup v (_links state) of
      Nothing -> scc v
      Just _  -> return ()

  scc v = do
    -- init
    Tarjan next stack links output <- get
    let stack' = v : stack
        links' = Map.insert v (next,next) links
        next' = next + 1
    put (Tarjan next' stack' links' output)

    -- successor vertices
    forM_ (Map.findWithDefault [] v graph) $ \w -> do
      state <- get 
      case Map.lookup w (_links state) of

        Nothing -> do
          scc w
          state <- get 
          let links = _links state 
          case Map.lookup v links of { Just (vi,vl) -> 
            case Map.lookup w links of { Just (_ ,wl) -> 
              put $ state { _links = Map.insert v (vi, min vl wl) links } } } 

        Just (wi,wl) -> when (w `elem` (_stack state)) $ do
          let links = _links state 
          case Map.lookup v links of { Just (vi,vl) -> 
            case Map.lookup w links of { Just (wi,_ ) -> 
              put $ state { _links = Map.insert v (vi, min vl wi) links } } } 

    -- pop and generate
    get >>= \state -> case Map.lookup v (_links state) of 
      Just (vi,vl) -> when (vi == vl) $ do
        Tarjan next stack links output <- get
        let (this , _v:stack') = span (/=v) stack      
        unless (_v == v) $ error "fatal"
        let output' = (v:this) : output
        put (Tarjan next stack' links output')

--------------------------------------------------------------------------------

