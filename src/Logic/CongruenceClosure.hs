{-# LANGUAGE FlexibleContexts #-}
module Logic.CongruenceClosure where

import           Prelude hiding (any)

import           Control.Arrow
import           Control.Applicative
import           Control.Monad hiding (unless)
import           Control.Monad.Trans.UnionFind (Point,runUnionFind,UnionFindT,fresh)
import qualified Control.Monad.Trans.UnionFind as U
import           Control.Monad.State hiding (unless)
import           Control.Monad.Writer hiding (unless)

import           Data.Foldable (traverse_)
import           Data.Maybe (fromJust)

import qualified PropLogic as PL

import           Text.Printf

import           Logic.Internal

figure1 :: (Functor m,MonadWriter [Logging] m) => m Satisfiability
figure1 =

  let a = Function "a" []
      b = Function "b" []
      abf = Function "f" [a,b]
      abfbf = Function "f" [abf,b]

  -- f(a,b) == a -> f(f(a,b),b) == a
  -- f(a,b) /= a \/ f(f(a,b),b) == a

  -- We show that the negation is unsatisfiable
  -- f(a,b) == a /\ f(f(a,b),b) /= a

  in decisionProcedure (Conjunctions [abf === a, abfbf =/= a])

decisionProcedure :: (Functor m,MonadWriter [Logging] m)
                  => Conjunctions -> m Satisfiability
decisionProcedure (Conjunctions conjunctions) = runUnionFind $ do
  gr <- termGraph conjunctions
  let (pos,neg) = partition gr positive conjunctions
  traverse_ (merge gr) pos

  anyEquiv <- any equivalent neg
  return $ if anyEquiv
    then Unsatisfiable
    else Satisfiable

merge :: (Functor m, MonadWriter [Logging] m)
      => Graph -> (Vert,Vert) -> UnionFindT String m ()
merge gr (u,v) = do

  tell [Merge u v]

  -- 1 If FIND(u) = FIND(v), then return
  unless (equivalent u v) $ do
    
    -- 2 Let Pu, be the set of all predecessors of all verttces equivalent to u,
    -- and Pv the set of all predecessors of all vertices equivalent to v.
    pu <- predOfAllVertEquivTo u
    pv <- predOfAllVertEquivTo v

    tell [ Pu pu, Pv pv ]

    -- 3 Call UNION(u, v)
    union u v

    -- 4 For each pair (x, y) such that x in Pu, and y in Pv,
    -- if FIND(x) /= FIND(y) but CONGRUENT(x, y) = TRUE, them merge(x,y)
    needsMerging <- filterM (notEquivalentButCongruent gr) [(x,y) | x <- pu, y <- pv]
    traverse_ (merge gr) needsMerging

  where
    predOfAllVertEquivTo vert =
      concatMap (predecessors gr) <$> filterM (equivalent vert) (vertices gr)

notEquivalentButCongruent :: (Functor m,Monad m) => Graph -> (Vert,Vert) -> UnionFindT String m Bool
notEquivalentButCongruent gr (x,y) = do
  notEquiv <- not <$> equivalent x y
  cong <- congruent gr x y
  return $ notEquiv && cong

congruent :: (Functor m,Monad m) => Graph -> Vert -> Vert -> UnionFindT String m Bool
congruent gr x y = do
  if outDegree gr x /= outDegree gr y
    then return False
    else and <$> zipWithM equivalent (successors gr x) (successors gr y)
