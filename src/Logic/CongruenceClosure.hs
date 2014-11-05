{-# LANGUAGE FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , MultiParamTypeClasses
           #-}
module Logic.CongruenceClosure where

import           Control.Arrow
import           Control.Applicative
import           Control.Monad hiding (unless)
import           Control.Monad.Trans.UnionFind (Point,runUnionFind,UnionFindT,fresh)
import qualified Control.Monad.Trans.UnionFind as U
import           Control.Monad.Writer hiding (unless)
import           Data.Foldable (traverse_)
import           Data.Graph.Inductive (mkGraph,Gr,LNode,Node)
import qualified Data.Graph.Inductive as G
import           Data.Maybe (fromJust)
import           Text.Printf

type Graph = Gr (Point String) Int
type Vert = LNode (Point String)

data Satisfiability = Satisfiable | Unsatisfiable
  deriving (Show,Eq)

figure1 :: (Functor m,MonadWriter [String] m) => m Satisfiability
figure1 = runUnionFind $ do
  [v1,v2,v3,v4] <- zipM [1..] [fresh "f",fresh "f",fresh "a",fresh "b"]

  --          v1 (f)
  --            / |
  --           /  |
  --      v2 (f)  |
  --         /\   |
  --        /  \  |
  --       /    \ |
  -- v3 (a)  v4 (b)
  let gr = mkGraph
            -- LNode = (Node,Payload)
            [ v1
            , v2
            , v3
            , v4
            ]
            -- LEdge = (Node,Node,Payload)
            [ (1,2,1)
            , (1,4,2)
            , (2,3,1)
            , (2,4,2)
            ]

  -- f(a,b) == a -> f(f(a,b),b) == a
  -- f(a,b) /= a \/ f(f(a,b),b) == a

  -- We show that the negation is unsatisfiable
  -- f(a,b) == a /\ f(f(a,b),b) /= a

  -- merge f(a,b) a
  merge gr v2 v3

  e <- not <$> equivalent v1 v3
  if e
    then return Satisfiable
    else return Unsatisfiable

merge :: (Functor m, MonadWriter [String] m)
      => Graph -> Vert -> Vert -> UnionFindT String m ()
merge gr u v = do
  tell [printf "merge(%d,%d)" (fst u) (fst v)]

  -- 1 If FIND(u) = FIND(v), then return
  unless (equivalent u v) $ do
    
    -- 2 Let Pu, be the set of all predecessors of all verttces equivalent to u,
    -- and Pv the set of all predecessors of all vertices equivalent to v.
    pu <- predOfAllVertEquivTo u
    pv <- predOfAllVertEquivTo v

    tell [ printf "P_%d = %s" (fst u) (show (map fst pu))
         , printf "P_%d = %s" (fst v) (show (map fst pv))
         ]

    -- 3 Call UNION(u, v)
    union u v

    -- 4 For each pair (x, y) such that x in Pu, and y in Pv,
    -- if FIND(x) /= FIND(y) but CONGRUENT(x, y) = TRUE, them merge(x,y)
    needsMerging <- filterM (notEquivalentButCongruent gr) [(x,y) | x <- pu, y <- pv]
    traverse_ (uncurry (merge gr)) needsMerging

  where
    predOfAllVertEquivTo vert =
      concatMap (predecessors gr) <$> filterM (\s -> equivalent s vert) (G.labNodes gr)

notEquivalentButCongruent :: (Functor m,Monad m) => Graph -> (LNode (Point String),LNode (Point String)) -> UnionFindT String m Bool
notEquivalentButCongruent gr (x,y) = do
  notEquiv <- not <$> equivalent x y
  cong <- congruent gr x y
  return $ notEquiv && cong

congruent :: (Functor m,Monad m) => Graph -> Vert -> Vert -> UnionFindT String m Bool
congruent gr x y = do
  if outdeg gr x /= outdeg gr y
    then return False
    else and <$> zipWithM equivalent (successors gr x) (successors gr y)

-- Wrapper functions

outdeg :: Graph -> Vert -> Int
outdeg gr (x,_) = G.outdeg gr x

label :: Graph -> Node -> Vert
label gr a = (a, fromJust (G.lab gr a))

equivalent :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT String m Bool
equivalent (_,x) (_,y) = U.equivalent x y

union :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT String m ()
union (_,x) (_,y) = U.union x y

predecessors :: Graph -> Vert -> [Vert]
predecessors gr (x,_) = label gr <$> G.pre gr x

successors :: Graph -> Vert -> [Vert]
successors gr (x,_) = label gr <$> G.suc gr x

-- Helper Instances
instance MonadWriter w m => MonadWriter w (UnionFindT p m) where
  writer = lift . writer
  tell   = lift . tell
  listen = mapUnionFindT listen
  pass   = mapUnionFindT pass

mapUnionFindT :: (Monad m, Monad n) => (m a -> n b) -> UnionFindT p m a -> UnionFindT p n b
mapUnionFindT f u = lift $ f (runUnionFind u)

-- Helper Functions

unless :: Monad m => m Bool -> m () -> m ()
unless mbool m = do
  b <- mbool
  if b
    then return ()
    else m

zipM :: (Functor m, Monad m) => [a] -> [m b] -> m [(a,b)]
zipM _       []      = return []
zipM []      _       = return []
zipM (a:as) (mb:mbs) = do
  b <- mb
  ((a,b):) <$> zipM as mbs
