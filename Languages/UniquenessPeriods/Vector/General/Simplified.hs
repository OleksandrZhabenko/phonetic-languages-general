-- |
-- Module      :  Languages.UniquenessPeriods.Vector.General.Simplified
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Simplified versions of the respective functions from the Languages.UniquenessPeriods.Vector.General.DebugG
-- module but they can be used basically once but not applied recursively to the same data (without additional processments).
--
{-# LANGUAGE BangPatterns, FlexibleContexts #-}

module Languages.UniquenessPeriods.Vector.General.Simplified (
  -- * Pure functions
  -- ** Self-recursive pure functions and connected with them ones
  maximumElBy
   -- ** Pure functions
  , maximumElByAll
  , maximumElGBy
  , maximumElByVec
  , maximumElByVecAll
) where

import Data.Foldable
import Data.Monoid
import Data.SubG
import qualified Data.Vector as VB
import Languages.UniquenessPeriods.Vector.AuxiliaryG
import Languages.UniquenessPeriods.Vector.StrictVG
import Languages.UniquenessPeriods.Vector.DataG
import  Languages.UniquenessPeriods.Vector.General.DebugG (uniquenessVariantsGN, equalSnDs)

-- | The function evaluates the 'VB.Vector' of 'UniquenessG1T2' @t@ @t2@ @a@ @b@ elements (related with the third argument) to retrieve the possibly maximum element
-- in it with respect to the order and significance (principality)  of the \"properties\" (represented as the functions @f :: [b] -> b@) being evaluated.
-- The most significant and principal is the \"property\", which index in the 'VB.Vector' of them is the 'Int' argument (so it is the first one) of the
-- function minus 1, then less significant is the next to the left \"property\" and so on.
-- The predefined library \"properties\" or related to them functions can be found in the package @phonetic-languages-properties@.
maximumElBy ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b) => Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> VB.Vector (UniquenessG1T2 t t2 a b) -- ^ The data to be analyzed.
  -> UniquenessG1T2 t t2 a b -- ^ The maximum element in respect with the given parameters.
maximumElBy k vN v
 | VB.null v = error "Languages.UniquenessPeriods.Vector.General.Simplified.maximumElBy: undefined for the empty second element in the tuple. "
 | compare k (VB.length vN) == GT = error "Languages.UniquenessPeriods.Vector.General.Simplified.maximumElBy: undefined for that amount of norms. "
 | compare k 0 == GT =
   let !maxK = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 (k - 1)) (VB.unsafeIndex vN1 (k - 1))) v
       vK = VB.filter (\(_,vN2,_) -> VB.unsafeIndex vN2 (k - 1) == VB.unsafeIndex (secondFrom3 maxK) (k - 1)) v in
         maximumElBy (k - 1) (VB.unsafeSlice 0 (k - 1) vN) vK
 | otherwise = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 0) (VB.unsafeIndex vN1 0)) v
{-# NOINLINE maximumElBy #-}

-- | Variant of the 'maximumElBy' function where all the given \"properties\" are used.
-- The predefined library \"properties\" or related to them functions can be found in the package @uniqueness-periods-vector-properties@.
maximumElByAll ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> VB.Vector (UniquenessG1T2 t t2 a b) -- ^ The data to be analyzed.
  -> UniquenessG1T2 t t2 a b -- ^ The maximum element according to the given \"properties\".
maximumElByAll vN = maximumElBy (VB.length vN) vN
{-# INLINE maximumElByAll #-}

-- | The function evaluates
-- the generated 'VB.Vector' of 'UniquenessG1T2' @t@ @t2@ @a@ @b@ elements to retrieve the possibly maximum element in it with respect to the order and significance (principality)
-- of the \"properties\" being evaluated. The most significant and principal is the \"property\", which index in the 'VB.Vector' of them is the 'Int' argument of the function
-- minus 1, then less significant is the next to the left \"property\" and so on.
maximumElGBy ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, UGG1 t (PreApp t a) a, Ord b, Show a, Show b) => t a -- ^ The \"whitespace symbols\" that delimit the subs in the 'Foldable' structure to be processed.
  -> a -- ^ The first \"whitespace symbol\" from the left.
  -> PreApp t a -- ^ A parameter to specify the lists to be prepended and postpended to the given data to be processed before actual processment.
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t a -- ^ The data to be processed.
  -> UniquenessG1T2 t t2 a b
maximumElGBy whspss hd rr f1 f2 f3 perms k vN frep v
 | compare k (VB.length vN) == GT = error "Languages.UniquenessPeriods.Vector.General.DebugG.maximumElGBy: undefined for that amount of norms. "
 | compare k 0 == GT =
   let vM = uniquenessVariants2GNPB (get1m rr) (get2m rr) hd f1 f2 f3 perms vN frep (subG whspss v)
       maxK = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 (k - 1)) (VB.unsafeIndex vN1 (k - 1))) vM
       vK = VB.filter (\(_,vN2,_) -> VB.unsafeIndex vN2 (k - 1) == VB.unsafeIndex (secondFrom3 maxK) (k - 1)) vM in
         maximumElBy (k - 1) (VB.unsafeSlice 0 (k - 1) vN) vK
 | otherwise = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 0) (VB.unsafeIndex vN1 0)) . uniquenessVariantsGN hd whspss f1 f2 f3 perms rr vN frep $ v

-- | Filters the last argument.
-- Finds out the group of maximum elements with respect of the @k@ \"properties\" (the most significant of which is the rightest one,
-- then to the left less significant etc.) of the second argument. The number of \"properties\" is given as the first argument. Then the function
-- rearranges the last argument by moving the elements equal by the second element in the triple to the maximum element to the first element in
-- the resulting tuple. The elements that are not equal to the maximum one are moved to the second element in the tuple.
-- If the second element of the tuple is empty, then just returns the last argument.
--
-- The last by significance \"property\" is the first element in the 'VB.Vector' of \"properties\" (@[b] -> b@) (so that the order of significance is
-- from the right to the left in the respective 'VB.Vector'). If the length of the vector of properties is greater than the first argument then
-- the last element(s) in the vector do not participate in producing the result (are ignored).
maximumElByVec ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> VB.Vector (UniquenessG1T2 t t2 a b) -- ^ The data to be analyzed.
  -> VB.Vector (UniquenessG1T2 t t2 a b)
maximumElByVec k vN v
 | VB.null v = VB.empty
 | otherwise = let !uniq = maximumElBy k vN v in let !snD = secondFrom3 uniq in VB.filter (equalSnDs snD . secondFrom3) v
{-# NOINLINE maximumElByVec #-}

-- | A variant of the 'maximumElByVec' where all the given \"properties\" are used.
maximumElByVecAll ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> VB.Vector (UniquenessG1T2 t t2 a b) -- ^ The data to be analyzed.
  -> VB.Vector (UniquenessG1T2 t t2 a b)
maximumElByVecAll vN = maximumElByVec (VB.length vN) vN
{-# INLINE maximumElByVecAll #-}

