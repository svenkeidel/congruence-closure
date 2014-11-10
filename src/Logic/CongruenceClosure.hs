{-# LANGUAGE FlexibleContexts, OverloadedLists, OverloadedStrings, TupleSections #-}
module Logic.CongruenceClosure where

import           Prelude hiding (any)

import           Control.Arrow
import           Control.Applicative
import           Control.Monad hiding (unless)
import           Control.Monad.Trans.UnionFind (Point,runUnionFind,UnionFindT,fresh)
import qualified Control.Monad.Trans.UnionFind as U
import           Control.Monad.State hiding (unless)
import           Control.Monad.Writer hiding (unless)

import           Data.Sequence (Seq)
import           Data.Foldable (traverse_)
import           Data.Maybe (fromJust)
import           Data.Text (Text)

import qualified PropLogic as PL

import           Text.Printf

import           Logic.Internal

-- Use `runDecisionProcedure figure1` to print out traces of the decision
-- procedure and show the satisfiability of the formula

figure1 :: (Functor m,MonadWriter (Seq Logging) m) => m Satisfiability
figure1 =

  let a = Function "a" []
      b = Function "b" []
      f x y = Function "f" [x,y]

  -- f(a,b) == a -> f(f(a,b),b) == a
  -- f(a,b) /= a \/ f(f(a,b),b) == a

  -- we show the validity of this formula by showing the unsatisfiability of its
  -- negation
  -- f(a,b) == a /\ f(f(a,b),b) /= a

  in decisionProcedure $ f a b === a /\ f (f a b) b =/= a

figure2 :: (Functor m,MonadWriter (Seq Logging) m) => m Satisfiability
figure2 =
  let
      a = Function "a" []
      f x = Function "f" [x]

  -- [f(f(f(a))) == a /\ f(f(f(f(f(a))))) == a] -> f(a) == a
  -- f(f(f(a))) /= a \/ f(f(f(f(f(a))))) /= a \/ f(a) == a

  -- we show the validity of this formula by showing the unsatisfiability of its
  -- negation
  -- f(f(f(a))) == a /\ f(f(f(f(f(a))))) == a /\ f(a) /= a

  in decisionProcedure $ f(f(f a)) === a
                      /\ f(f(f(f(f a)))) === a
                      /\ f a =/= a

decisionProcedure :: (Functor m,MonadWriter (Seq Logging) m)
                  => Conjunctions -> m Satisfiability
decisionProcedure (Conjunctions conjunctions) = runUnionFind $ do
    gr <- termGraph conjunctions
    let (pos,neg) = partition gr positive conjunctions
    traverse_ (merge gr) pos

    anyEquiv <- any equivalent neg
    return $ if anyEquiv
      then Unsatisfiable
      else Satisfiable

merge :: (Functor m, MonadWriter (Seq Logging) m)
      => Graph -> (Vert,Vert) -> UnionFindT Text m ()
merge gr (u,v) = do

  tell [Merge gr u v]

  -- 1 If FIND(u) = FIND(v), then return
  unless (equivalent u v) $ do
    
    -- 2 Let Pu, be the set of all predecessors of all verttces equivalent to u,
    -- and Pv the set of all predecessors of all vertices equivalent to v.
    pu <- predOfAllVertEquivTo u
    pv <- predOfAllVertEquivTo v

    tell [ Pu gr pu, Pv gr pv ]

    -- 3 Call UNION(u, v)
    union u v

    tell [ Union gr u v ]

    -- 4 For each pair (x, y) such that x in Pu, and y in Pv,
    -- if FIND(x) /= FIND(y) but CONGRUENT(x, y) = TRUE, them merge(x,y)
    needsMerging <- filterM (notEquivalentButCongruent gr) [(x,y) | x <- pu, y <- pv]
    traverse_ (merge gr) needsMerging

  where
    predOfAllVertEquivTo vert =
      concatMap (predecessors gr) <$> filterM (equivalent vert) (vertices gr)

notEquivalentButCongruent :: (Functor m,Monad m) => Graph -> (Vert,Vert) -> UnionFindT Text m Bool
notEquivalentButCongruent gr (x,y) = do
  notEquiv <- not <$> equivalent x y
  cong <- congruent gr x y
  return $ notEquiv && cong

congruent :: (Functor m,Monad m) => Graph -> Vert -> Vert -> UnionFindT Text m Bool
congruent gr x y = do
  if outDegree gr x /= outDegree gr y
    then return False
    else and <$> zipWithM equivalent (successors gr x) (successors gr y)
