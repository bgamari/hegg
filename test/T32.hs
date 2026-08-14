{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}
module T32 where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Equality.Utils
import Data.Equality.Matching
import Data.Equality.Saturation
import Data.Equality.Graph
import qualified Data.Equality.Graph as EG
import Data.Equality.Saturation.Scheduler
  ( Scheduler (..)
  , defaultBackoffScheduler
  , rulesWereBanned
  )
import Data.Equality.Graph.Monad
import qualified Data.IntMap.Strict as IM

data SymExpr a = Symbol String
               | a :+: a
               deriving (Functor, Foldable, Traversable, Eq, Ord, Show)
infix 6 :+:

data TestScheduler
  = RetryTrapScheduler
  | DeferredRuleScheduler
  | BoundaryRuleScheduler
  | ExpiredRuleScheduler

instance Scheduler SymExpr TestScheduler where
  data Stat SymExpr TestScheduler
    = RetryTrapStat
    | DeferredRuleStat
    | BoundaryRuleStat
    | ExpiredRuleStat

  updateStats scheduler iteration rewriteId _ _ stats matches =
    case scheduler of
      RetryTrapScheduler
        | null matches -> stats
        | otherwise -> IM.insert rewriteId RetryTrapStat stats
      DeferredRuleScheduler
        | iteration == 1 && rewriteId == 2 ->
            error "saturation discarded scheduler stats"
        | iteration == 0 && rewriteId == 2 ->
            IM.insert rewriteId DeferredRuleStat stats
        | otherwise -> stats
      BoundaryRuleScheduler
        | iteration == 0 && rewriteId == 2 ->
            IM.insert rewriteId BoundaryRuleStat stats
        | otherwise -> stats
      ExpiredRuleScheduler
        | iteration >= 2 -> error "saturation retried an expired rule"
        | iteration == 0 -> IM.insert rewriteId ExpiredRuleStat stats
        | otherwise -> stats

  isBanned iteration = \case
    RetryTrapStat
      | iteration == 0 -> True
      | otherwise -> error "saturation retried an enabled saturated pass"
    DeferredRuleStat -> iteration >= 1
    BoundaryRuleStat -> iteration == 1
    ExpiredRuleStat -> False

-- This test tests that using "VariablePattern 1, VariablePattern 2,
-- VariablePattern 3" in a rewrite rule succeeds, as opposed to using the
-- IsString instance for Pattern.
-- (Well, it tests that we can no longer screw up by writing the numbers
-- directly as well. Now the implementation transforms the strings into Ids
-- when compiling the pattern)
rewrites :: [Rewrite () SymExpr]
rewrites =
  [ pat (VariablePattern "1" :+: pat (VariablePattern "2" :+: VariablePattern "3")) := pat (pat (VariablePattern "1" :+: VariablePattern "2") :+: VariablePattern "3")
  ]

e1, e1' :: Fix SymExpr
e1 = Fix (Fix (Fix (Symbol "a") :+: Fix (Symbol "b")) :+: Fix (Symbol "c"))
e1' = Fix (Fix (Symbol "a") :+: Fix (Fix (Symbol "b") :+: Fix (Symbol "c")))

somePattern :: Pattern []
somePattern = NonVariablePattern [VariablePattern "0",VariablePattern "1"]

-- Test basic associativity using pattern vars
testT32 :: TestTree
testT32 = testGroup "T32"
    [ testCase "basic associativity with VarPattern 1,2,3" $
        let
          (e1_id, eg0)  = EG.represent @() e1 emptyEGraph
          (e1'_id, eg1) = EG.represent @() e1' eg0
          ((), eg2)     = runEGraphM eg1 (runEqualitySaturation defaultBackoffScheduler rewrites)
          e1_canon      = EG.find e1_id eg2
          e1'_canon     = EG.find e1'_id eg2
         in e1_canon @?= e1'_canon
    , testCase "stops after a fully enabled saturated pass" $
        let
          value = Fix $ Symbol "x"
          (valueId, eg0) = EG.represent @() value emptyEGraph
          ((), eg1) =
            runEGraphM
              eg0
              ( runEqualitySaturation
                  RetryTrapScheduler
                  [pat (Symbol "x") := pat (Symbol "x")]
              )
         in EG.find valueId eg1 @?= valueId
    , testCase "retries after saturating with a banned rule" $ do
        rulesWereBanned @SymExpr @TestScheduler 1 IM.empty
          @?= False
        rulesWereBanned
          @SymExpr
          @TestScheduler
          1
          (IM.fromList [(1, ExpiredRuleStat), (2, DeferredRuleStat)])
          @?= True
        rulesWereBanned @SymExpr @TestScheduler 1 (IM.singleton 2 DeferredRuleStat)
          @?= True
        let
          value = Fix $ Symbol "seed"
          (valueId, eg0) = EG.represent @() value emptyEGraph
          ((), eg1) =
            runEGraphM
              eg0
              ( runEqualitySaturation
                  DeferredRuleScheduler
                  [ pat (Symbol "seed") := pat (Symbol "ready")
                  , pat (Symbol "ready") := pat (Symbol "done")
                  ]
              )
          (doneId, eg2) = EG.represent @() (Fix $ Symbol "done") eg1
        EG.find doneId eg2 @?= EG.find valueId eg2
    , testCase "retries on the final banned iteration" $ do
        rulesWereBanned @SymExpr @TestScheduler 1 (IM.singleton 2 BoundaryRuleStat)
          @?= True
        rulesWereBanned @SymExpr @TestScheduler 2 (IM.singleton 2 BoundaryRuleStat)
          @?= False
        let
          value = Fix $ Symbol "seed"
          (valueId, eg0) = EG.represent @() value emptyEGraph
          ((), eg1) =
            runEGraphM
              eg0
              ( runEqualitySaturation
                  BoundaryRuleScheduler
                  [ pat (Symbol "seed") := pat (Symbol "ready")
                  , pat (Symbol "ready") := pat (Symbol "done")
                  ]
              )
          (doneId, eg2) = EG.represent @() (Fix $ Symbol "done") eg1
        EG.find doneId eg2 @?= EG.find valueId eg2
    , testCase "stops after saturating with expired scheduler stats" $ do
        rulesWereBanned @SymExpr @TestScheduler 1 (IM.singleton 1 ExpiredRuleStat)
          @?= False
        let
          value = Fix $ Symbol "seed"
          (valueId, eg0) = EG.represent @() value emptyEGraph
          ((), eg1) =
            runEGraphM
              eg0
              ( runEqualitySaturation
                  ExpiredRuleScheduler
                  [pat (Symbol "seed") := pat (Symbol "ready")]
              )
          (readyId, eg2) = EG.represent @() (Fix $ Symbol "ready") eg1
        EG.find readyId eg2 @?= EG.find valueId eg2
    -- , testCase "compiling pattern" $
    --     compileToQuery somePattern @?= Query ...
    ]
