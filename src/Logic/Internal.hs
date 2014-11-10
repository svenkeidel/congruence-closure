{-# LANGUAGE ViewPatterns
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
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
import           Data.Sequence (Seq,ViewL(..))
import qualified Data.Sequence as S
import           Data.Maybe (fromJust)
import           Data.Foldable (traverse_)
import           Data.Traversable (traverse)
import           Data.Graph.Inductive hiding (Graph)
import           Data.Graph.Inductive.NodeMap
import           Data.Text(Text,unpack)

import           GHC.Exts

newtype Conjunctions = Conjunctions [Equation]
data Equation = Equal Term Term
              | NotEqual Term Term
data Term = Function Text [Term]
  deriving (Eq,Ord)

data Satisfiability = Satisfiable | Unsatisfiable
  deriving (Show,Eq)

(===) :: Term -> Term -> Equation
(===) = Equal
infix 4 ===

(=/=) :: Term -> Term -> Equation
(=/=) = NotEqual
infix 4 =/=

instance Show Term where
  show (Function sym []) = unpack sym
  show (Function sym childs) =
    unpack sym ++ "(" ++ concat (L.intersperse "," (map show childs)) ++ ")"

class Conjunction a where
  (/\) :: Equation -> a -> Conjunctions
  infixr 3 /\

instance Conjunction Equation where
  (/\) e1 e2 = Conjunctions [e1, e2]

instance Conjunction Conjunctions where
  (/\) e1 (Conjunctions e2) = Conjunctions (e1:e2)

newtype Graph = Graph (NodeMap Term,Gr (Text,Point Text) Int)
newtype Vert = Vert (LNode (Text,Point Text))

interleave :: [(a,a)] -> [a]
interleave ((x,y):rest) = x : y : interleave rest
interleave []           = []

termGraph :: (Functor m,Monad m) => [Equation] -> UnionFindT Text m Graph
termGraph = termGraph' . interleave . terms

termGraph' :: (Functor m,Monad m) => [Term] -> UnionFindT Text m Graph
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
      return (node,(name,var))

vertex :: Graph -> Term -> Vert
vertex gr@(Graph (nodeMap,_)) term =
  let (node,_) = mkNode_ nodeMap term
  in label gr node

graph :: Graph -> Gr (Text,Point Text) Int
graph (Graph (_,gr)) = gr

vertices :: Graph -> [Vert]
vertices = map Vert . labNodes . graph

outDegree :: Graph -> Vert -> Int
outDegree (graph -> gr) (Vert (x,_)) = outdeg gr x

label :: Graph -> Node -> Vert
label (graph -> gr) a = Vert (a, fromJust (lab gr a))

equivalent :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT Text m Bool
equivalent (Vert (_,(_,x))) (Vert (_,(_,y))) = U.equivalent x y

union :: (Functor m, Monad m) => Vert -> Vert -> UnionFindT Text m ()
union (Vert (_,(_,x))) (Vert (_,(_,y))) = U.union x y

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

term :: Graph -> Vert -> Term
term (Graph (_,gr)) (Vert (n,_)) = go gr n
  where
    go :: Gr (Text,a) Int -> Node -> Term
    go gr n =
      case match n gr of
        (Nothing,_) -> error "context is Nothing"
        (Just (_,_,(sym,_),out),gr') ->
          Function sym $ map (go gr') $ sortEdges out
    sortEdges out = map snd $ L.sortBy (comparing fst) out

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
  = Merge Graph Vert Vert
  | Pu Graph [Vert]
  | Pv Graph [Vert]
  | Union Graph Vert Vert

instance Show Logging where
  show (Merge gr u v) = "merge " ++ show (term gr u) ++ " " ++ show (term gr v)
  show (Union gr u v) = "union " ++ show (term gr u) ++ " " ++ show (term gr v)
  show (Pu gr pu) = "pu " ++ show (map (term gr) pu)
  show (Pv gr pv) = "pv " ++ show (map (term gr) pv)

runDecisionProcedure :: Writer (Seq Logging) Satisfiability -> IO ()
runDecisionProcedure decision = do
  let (sat,logs) = runWriter decision
  putStrLn $ unlines $ map show $ toList logs
  putStrLn $ show sat

instance IsList (Seq a) where
  type Item (Seq a) = a
  fromList = S.fromList
  toList s = case S.viewl s of
    EmptyL  -> []
    x :< xs -> x : toList xs
