{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module MatchingDatabase (matchingDatabaseTests) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import Test.Tasty
import Test.Tasty.HUnit

import Data.Equality.Graph.Nodes (Operator (..))
import Data.Equality.Matching.Database

data MatchLang a = MatchNode Int [a]
  deriving (Eq, Foldable, Functor, Ord, Traversable)

matchingDatabaseTests :: TestTree
matchingDatabaseTests =
  testGroup
    "Matching database"
    [ testCase
        "deduplicates reordered variables"
        reorderedVariablesAreDeduplicated
    , testCase
        "does not duplicate matches across conjuncts"
        conjunctiveJoinReturnsOneSubstitution
    ]

reorderedVariablesAreDeduplicated :: Assertion
reorderedVariablesAreDeduplicated =
  case genericJoin database query of
    [subst] -> do
      sizeSubst subst @?= length distinctVariables
      findSubst rootVariable subst @?= rootClass
      mapM_
        (\variable -> findSubst variable subst @?= classFor variable)
        distinctVariables
    matches ->
      assertFailure $
        "expected one match, got " <> show (length matches)
 where
  rootVariable = MatchVar 0
  rootClass = classFor rootVariable
  distinctVariables = MatchVar <$> [0 .. 64]
  reorderedVariables =
    MatchVar 64 : MatchVar 1 : MatchVar 64 : (MatchVar <$> [2 .. 63])
  classFor (MatchVar variable) = 100 + variable
  childClasses = classFor <$> reorderedVariables
  database = singletonRelationDatabase 0 (rootClass : childClasses)
  query =
    Query
      []
      [ Atom
          (CVar rootVariable)
          (MatchNode 0 (CVar <$> reorderedVariables))
      ]

conjunctiveJoinReturnsOneSubstitution :: Assertion
conjunctiveJoinReturnsOneSubstitution =
  case genericJoin database query of
    [subst] -> findSubst variable subst @?= classId
    matches ->
      assertFailure $
        "expected one substitution, got " <> show (length matches)
 where
  variable = MatchVar 0
  classId = 7
  database =
    DB $
      M.fromList
        [ (Operator (MatchNode 0 []), singletonRow [classId])
        , (Operator (MatchNode 1 []), singletonRow [classId])
        ]
  query =
    Query
      []
      [ Atom (CVar variable) (MatchNode 0 [])
      , Atom (CVar variable) (MatchNode 1 [])
      ]

singletonRelationDatabase :: Int -> [Int] -> Database MatchLang
singletonRelationDatabase tag row =
  DB $
    M.singleton
      (Operator (MatchNode tag (replicate (length row - 1) ())))
      (singletonRow row)

singletonRow :: [Int] -> IntTrie
singletonRow [] = MkIntTrie IS.empty IM.empty
singletonRow (value : rest) =
  MkIntTrie
    (IS.singleton value)
    (IM.singleton value (singletonRow rest))
