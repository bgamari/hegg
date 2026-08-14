{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}

module Extraction (extractionTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Data.Equality.Analysis ()
import Data.Equality.Extraction (CostFunction, extractBest)
import qualified Data.Equality.Graph as G
import qualified Data.Equality.Graph.Monad as EG
import Data.Equality.Utils (Fix (..))

data Expr a
  = Atom Int
  | Poison
  | Wrap a
  | Pair a a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

exprCost :: CostFunction Expr Int
exprCost = \case
  Atom value -> value
  Poison -> error "unreachable extraction cost evaluated"
  Wrap value -> value + 1
  Pair left right -> left + right + 1

atom :: Int -> Fix Expr
atom = Fix . Atom

wrap :: Fix Expr -> Fix Expr
wrap = Fix . Wrap

unreachableCostIsNotEvaluated :: IO ()
unreachableCostIsNotEvaluated =
  extractBest egraph exprCost root @?= wrap (atom 1)
 where
  (root, egraph) = result
  result :: (G.ClassId, G.EGraph () Expr)
  result = EG.egraph $ do
    rootClass <- EG.represent $ wrap (atom 1)
    _ <- EG.represent $ Fix Poison
    EG.rebuild
    pure rootClass

extractsAcrossStaleMergesAndCycles :: IO ()
extractsAcrossStaleMergesAndCycles =
  extractBest egraph exprCost root @?= wrap (wrap (atom 1))
 where
  (root, egraph) = result
  result :: (G.ClassId, G.EGraph () Expr)
  result = EG.egraph $ do
    oldLeaf <- EG.add $ G.Node $ Atom 9
    newLeaf <- EG.add $ G.Node $ Atom 1

    -- Ensure newLeaf leads the merge while finite retains oldLeaf's ID.
    _ <- EG.add $ G.Node $ Wrap newLeaf
    _ <- EG.add $ G.Node $ Pair newLeaf newLeaf
    finite <- EG.add $ G.Node $ Wrap oldLeaf
    _ <- EG.merge oldLeaf newLeaf

    rootClass <- EG.add $ G.Node $ Wrap finite
    cyclicAlternative <- EG.add $ G.Node $ Wrap rootClass
    _ <- EG.merge rootClass cyclicAlternative
    pure rootClass

extractionTests :: TestTree
extractionTests =
  testGroup
    "Extraction"
    [ testCase "does not evaluate unreachable costs" unreachableCostIsNotEvaluated
    , testCase
        "handles stale merges and cyclic alternatives"
        extractsAcrossStaleMergesAndCycles
    ]
