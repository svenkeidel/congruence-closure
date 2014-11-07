{-# LANGUAGE ViewPatterns
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , MultiParamTypeClasses
           #-}
module Logic.Internal where

import           Prelude hiding (any)

import           Control.Arrow
import           Control.Applicative hiding (empty)
import           Control.Monad
import           Control.Monad.Trans.UnionFind (Point,runUnionFind,UnionFindT,fresh)
import qualified Control.Monad.Trans.UnionFind as U
import           Control.Monad.Writer hiding (unless)

import           Data.Ord
import qualified Data.List as L
import           Data.Maybe (fromJust)
import           Data.Foldable (traverse_)
import           Data.Traversable (traverse)
import           Data.Graph.Inductive hiding (Graph)
import           Data.Graph.Inductive.NodeMap

newtype Conjunctions = Conjunctions [Equation]
data Equation = Equal Term Term
              | NotEqual Term Term
data Term = Function String [Term]
  deriving (Eq,Ord)

data Satisfiability = Satisfiable | Unsatisfiable
  deriving (Show,Eq)

(===) :: Term -> Term -> Equation
(===) = Equal

(=/=) :: Term -> Term -> Equation
(=/=) = NotEqual

instance Show Term where
  show (Function sym []) = sym
  show (Function sym childs) = sym ++ show childs

newtype Graph = Graph (NodeMap Term,Gr (Point String) Int)
newtype Vert = Vert (LNode (Point String))

interleave :: [(a,a)] -> [a]
interleave ((x,y):rest) = x : y : interleave rest
interleave []           = []

termGraph :: (Functor m,Monad m) => [Equation] -> UnionFindT String m Graph
termGraph = termGraph' . interleave . terms

termGraph' :: (Functor m,Monad m) => [Term] -> UnionFindT String m Graph
termGraph' ts = do
  let (nodeMap, gr) = snd $ run empty $ traverse_ insertTerm ts
  vars <- traverse genVars (labNodes gr)
  return $ Graph (nodeMap, mkGraph vars (labEdges gr))
  where
    insertTerm :: Term -> NodeMapM Term Int Gr ()
    insertTerm term@(Function name childs) = do
      insMapNodeM term
      forM_ (zip childs [1..]) $ \(child,i) -> do
        insMapNodeM child
        insMapEdgeM (term,child,i)
        insertTerm child

    genVars (node, Function name _) = do
      var <- fresh name
      return (node,var)

vertex :: Graph -> Term -> Vert
vertex gr@(Graph (nodeMap,_)) term =
  let (node,_) = mkNode_ nodeMap term
  in label gr node

graph :: Graph -> Gr (Point String) Int
graph (Graph (_,gr)) = gr

vertices :: Graph -> [Vert]
vertices = map Vert . labNodes . graph

outDegree :: Graph -> Vert -> Int
outDegree (graph -> gr) (Vert (x,_)) = outdeg gr x

label :: Graph -> Node -> Vert
label (graph -> gr) a = Vert (a, fromJust (lab gr a))

equivalent :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT String m Bool
equivalent (Vert (_,x)) (Vert (_,y)) = U.equivalent x y

union :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT String m ()
union (Vert (_,x)) (Vert (_,y)) = U.union x y

predecessors :: Graph -> Vert -> [Vert]
predecessors gr (Vert (x,_)) = label gr <$> pre (graph gr) x

successors :: Graph -> Vert -> [Vert]
successors gr (Vert (x,_)) = label gr <$> suc (graph gr) x

terms :: [Equation] -> [(Term,Term)]
terms = map go
  where
    go e = case e of
      Equal t1 t2    -> (t1,t2)
      NotEqual t1 t2 -> (t1,t2)

partition :: Graph -> (Equation -> Bool) -> [Equation] -> ([(Vert,Vert)],[(Vert,Vert)])
partition gr f equations =
  let (as,bs) = L.partition f equations
  in (map (vertex gr *** vertex gr) $ terms as, map (vertex gr *** vertex gr) $ terms bs)

unless :: Monad m => m Bool -> m () -> m ()
unless mbool m = do
  b <- mbool
  if b
    then return ()
    else m

instance Show Vert where
  show (Vert (n,_)) = show n

instance MonadWriter w m => MonadWriter w (UnionFindT p m) where
  writer = lift . writer
  tell   = lift . tell
  listen = mapUnionFindT listen
  pass   = mapUnionFindT pass

mapUnionFindT :: (Monad m, Monad n) => (m a -> n b) -> UnionFindT p m a -> UnionFindT p n b
mapUnionFindT f u = lift $ f (runUnionFind u)

positive :: Equation -> Bool
positive t =
  case t of
    Equal _ _    -> True
    NotEqual _ _ -> False

any :: Monad m => (a -> b -> m Bool) -> [(a,b)] -> m Bool
any _ [] = return False
any f ((a,b):abs) = do
  r <- f a b
  if r
    then return True
    else any f abs

data Logging
  = Merge Vert Vert
  | Pu [Vert]
  | Pv [Vert]
  deriving Show
