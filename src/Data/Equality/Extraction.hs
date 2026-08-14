{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- |
--    Given an e-graph representing expressions of our language, we might want to
--    extract, out of all expressions represented by some equivalence class, /the best/
--    expression (according to a 'CostFunction') represented by that class
--
--    The function 'extractBest' allows us to do exactly that: get the best
--    expression represented in an e-class of an e-graph given a 'CostFunction'
module Data.Equality.Extraction
  ( -- * Extraction
    extractBest

    -- * Cost
  , CostFunction
  , depthCost
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S

import Data.Equality.Graph
import Data.Equality.Graph.Internal (EGraph (classes))
import Data.Equality.Utils

-- vvvv and necessarily all the best sub-expressions from children equilalence classes

-- | Extract the /best/ expression from an equivalence class according to a
-- 'CostFunction'
--
-- @
-- (i, egr) = ...
--    i <- represent expr
--            ...
--
-- bestExpr = extractBest egr 'depthCost' i
-- @
--
-- For a real example you might want to check out the source code of 'Data.Equality.Saturation.equalitySaturation''
extractBest
  :: forall anl lang cost
   . (Language lang, Ord cost)
  => EGraph anl lang
  -- ^ The e-graph out of which we are extracting an expression
  -> CostFunction lang cost
  -- ^ The cost function to define /best/
  -> ClassId
  -- ^ The e-class from which we'll extract the expression
  -> Fix lang
  -- ^ The resulting /best/ expression, in its fixed point form.
extractBest egr cost (flip find egr -> i) =
  -- Only descendants of the target class can contribute to an extracted
  -- expression. Restricting the fixed point to that closure avoids revisiting
  -- unrelated roots when several expressions share one e-graph.
  let allCosts = findCosts reachableEClasses mempty
   in case findBest i allCosts of
        Just best ->
          case reconstruct allCosts S.empty i of
            Just expr -> expr
            Nothing -> bestWitness best
        Nothing -> error $ "Couldn't find a best node for e-class " <> show i
 where
  reachableEClasses :: ClassIdMap (EClass anl lang)
  reachableEClasses = reachableClasses i

  reachableClasses :: ClassId -> ClassIdMap (EClass anl lang)
  reachableClasses root = go IM.empty [root]
   where
    go found [] = found
    go found (rawClassId : pending)
      | IM.member classId found = go found pending
      | otherwise =
          case IM.lookup classId (classes egr) of
            Nothing ->
              error $
                "extractBest: missing canonical e-class " <> show classId
            Just eclass ->
              let childClasses =
                    [ find child egr
                    | node <- S.toList $ eClassNodes eclass
                    , child <- children node
                    ]
               in go
                    (IM.insert classId eclass found)
                    (childClasses <> pending)
     where
      classId = find rawClassId egr

  -- \| Find the lowest cost of all e-classes in an e-graph in an extraction
  findCosts
    :: ClassIdMap (EClass anl lang)
    -> ClassIdMap (Best lang cost)
    -> ClassIdMap (Best lang cost)
  findCosts eclasses current =
    let (modified, updated) = IM.foldlWithKey' f (False, current) eclasses

        {-# INLINE f #-}
        f
          :: (Bool, ClassIdMap (Best lang cost))
          -> Int
          -> EClass anl lang
          -> (Bool, ClassIdMap (Best lang cost))
        f acc@(_, beingUpdated) i' EClass{eClassNodes = nodes} =
          let
            currentCost = IM.lookup i' beingUpdated

            newCost =
              S.foldl'
                ( \c n -> case (c, nodeTotalCost beingUpdated n) of
                    (Nothing, Nothing) -> Nothing
                    (Nothing, Just nc) -> Just nc
                    (Just oc, Nothing) -> Just oc
                    (Just oc, Just nc)
                      | bestCost nc < bestCost oc -> Just nc
                      | otherwise -> Just oc
                )
                Nothing
                nodes
           in
            -- Current cost + get lowest cost and corresponding node of an e-class if possible
            case (currentCost, newCost) of
              (Nothing, Just new) -> (True, IM.insert i' new beingUpdated)
              (Just old, Just new)
                | bestCost new < bestCost old ->
                    (True, IM.insert i' new beingUpdated)
              _ -> acc
     in -- If any class was modified, loop
        if modified
          then findCosts eclasses updated
          else updated

  -- \| Get the total cost of a node in an e-graph if possible at this stage of
  -- the extraction
  --
  -- For a node to have a cost, all its (canonical) sub-classes have a best
  -- candidate. Retain the selected node and a finite expression for cycle
  -- fallback while the fixed point converges.
  nodeTotalCost
    :: Traversable lang
    => ClassIdMap (Best lang cost) -> ENode lang -> Maybe (Best lang cost)
  nodeTotalCost m node@(Node n) = do
    childBest <- traverse ((`IM.lookup` m) . flip find egr) n
    pure $
      Best
        { bestCost = cost $ bestCost <$> childBest
        , bestNode = node
        , bestWitness = Fix $ bestWitness <$> childBest
        }
  {-# INLINE nodeTotalCost #-}

  reconstruct
    :: ClassIdMap (Best lang cost)
    -> S.Set ClassId
    -> ClassId
    -> Maybe (Fix lang)
  reconstruct bestByClass visiting rawClassId =
    case IM.lookup classId bestByClass of
      Nothing ->
        error $
          "extractBest: missing best node for e-class " <> show classId
      Just Best{bestNode = Node node, bestWitness = witness}
        | S.member classId visiting -> Just witness
        | otherwise ->
            Fix
              <$> traverse
                (reconstruct bestByClass $ S.insert classId visiting)
                node
   where
    classId = find rawClassId egr
{-# INLINEABLE extractBest #-}

-- | A cost function is used to attribute a cost to representations in the
-- e-graph and to extract the best one.
--
-- The cost function is polymorphic over the type used for the cost, however
-- @cost@ must instance 'Ord' in order for the defined 'CostFunction' to
-- fulfill its purpose. That's why we have an @Ord cost@ constraint in
-- 'Data.Equality.Saturation.equalitySaturation' and 'extractBest'
--
-- === Example
-- @
-- symCost :: Expr Int -> Int
-- symCost = \case
--     BinOp Integral e1 e2 -> e1 + e2 + 20000
--     BinOp Diff e1 e2 -> e1 + e2 + 500
--     BinOp x e1 e2 -> e1 + e2 + 3
--     UnOp x e1 -> e1 + 30
--     Sym _ -> 1
--     Const _ -> 1
-- @
type CostFunction l cost = l cost -> cost

-- | Simple cost function: the deeper the expression, the bigger the cost
depthCost :: Language l => CostFunction l Int
depthCost = (+ 1) . sum
{-# INLINE depthCost #-}

-- | Find the current best node and its cost in an equivalence class given only the class and the current extraction
-- This is not necessarily the best node in the e-graph, only the best in the current extraction state
findBest :: ClassId -> ClassIdMap (Best lang a) -> Maybe (Best lang a)
findBest = IM.lookup
{-# INLINE findBest #-}

data Best lang cost = Best
  { bestCost :: cost
  , bestNode :: ENode lang
  , bestWitness :: Fix lang
  }
