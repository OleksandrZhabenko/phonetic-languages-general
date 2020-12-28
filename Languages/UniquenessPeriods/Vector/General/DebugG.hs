-- |
-- Module      :  Languages.UniquenessPeriods.Vector.General.DebugG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Generalization of the functionality of the DobutokO.Poetry.General.Debug
-- module from the @dobutokO-poetry-general-languages@ package.
--
{-# LANGUAGE BangPatterns, FlexibleContexts #-}

module Languages.UniquenessPeriods.Vector.General.DebugG (
  -- * Pure functions
  -- ** Self-recursive pure functions and connected with them ones
  maximumElBy
  , uniqNPropertiesN
  , uniqNPropertiesNAll
  , uniqNProperties2GN
  -- ** Pure functions
  , maximumElByAll
  , maximumElGBy
  , uniquenessVariantsGN
  , maximumElByVec
  , maximumElByVecAll
  -- * IO functions
  -- ** Printing subsystem
  , toFile
  , toFileStr
  , printUniquenessG1
  , printUniquenessG1List
  -- *** With 'String'-based arguments
  , printUniquenessG1ListStr
  -- *** With 'VB.Vector' 'Char' based arguments
  , printUniquenessG1VChar
  -- *** Auxiliary functions
  , newLineEnding
  , equalSnDs
) where

import Data.Foldable
import Data.Monoid
import Data.SubG
import Data.Print.Info
import System.IO
import qualified Data.Vector as VB
import Languages.UniquenessPeriods.Vector.AuxiliaryG
import Languages.UniquenessPeriods.Vector.StrictVG
import Languages.UniquenessPeriods.Vector.DataG

-- | The function evaluates the 'VB.Vector' of 'UniquenessG1T2' @t@ @t2@ @a@ @b@ elements (related with the third argument) to retrieve the possibly maximum element
-- in it with respect to the order and significance (principality)  of the \"properties\" (represented as the functions @f :: [b] -> b@) being evaluated.
-- The most significant and principal is the \"property\", which index in the 'VB.Vector' of them is the 'Int' argument (so it is the first one) of the
-- function minus 1, then less significant is the next to the left \"property\" and so on.
-- The predefined library \"properties\" or related to them functions can be found in the package @phonetic-languages-properties@.
maximumElBy ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b) => Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  ->  UniqG2T2 t t2 a b -- ^ The data to be analyzed.
  -> UniquenessG1T2 t t2 a b -- ^ The maximum element in respect with the given parameters.
maximumElBy k vN y
 | VB.null . snd . get22 $ y = error "Languages.UniquenessPeriods.Vector.General.DebugG.maximumElBy: undefined for the empty second element in the tuple. "
 | compare k (VB.length vN) == GT = error "Languages.UniquenessPeriods.Vector.General.DebugG.maximumElBy: undefined for that amount of norms. "
 | compare k 0 == GT =
   let !maxK = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 (k - 1)) (VB.unsafeIndex vN1 (k - 1))) . snd . get22 $ y
       vK = VB.filter (\(_,vN2,_) -> VB.unsafeIndex vN2 (k - 1) == VB.unsafeIndex (secondFrom3 maxK) (k - 1)) . snd . get22 $ y in
         maximumElBy (k - 1) (VB.unsafeSlice 0 (k - 1) vN) (UL2 (fst . get22 $ y,vK))
 | otherwise = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 0) (VB.unsafeIndex vN1 0)) . snd . get22 $ y
{-# NOINLINE maximumElBy #-}

-- | Prints every element from the structure on the new line to the file. Uses 'appendFile' function inside.
toFile ::
  (Foldable t, Show (t a), Monoid (t a)) => FilePath -- ^ The 'FilePath' to the file to be written in the 'AppendMode' (actually appended with) the information output.
  -> t (t a) -- ^ Each element is appended on the new line to the file.
  -> IO ()
toFile file xss = mapM_ (\xs -> appendFile file (show xs `mappend` newLineEnding)) xss

-- | Prints every 'String' from the list on the new line to the file. Uses 'appendFile' function inside.
toFileStr ::
  FilePath -- ^ The 'FilePath' to the file to be written in the 'AppendMode' (actually appended with) the information output.
  -> [String] -- ^ Each 'String' is appended on the new line to the file.
  -> IO ()
toFileStr file xss = mapM_ (\xs -> appendFile file (xs `mappend` newLineEnding)) xss

-- | Is used to print output specified to the 'stdout' or to the 'FilePath' specified as the inner argument in the 'Info2' parameter.
printUniquenessG1
  :: (Show (t a), Show b, Show (t2 b)) => Info2 -- ^ A parameter to control the predefined behaviour of the printing. The 'I1' branch prints to the 'stdout' and the 'I2' - to the file.
  -> UniquenessG1T2 t t2 a b -- ^ The element, for which the information is printed.
  -> IO ()
printUniquenessG1 info uni
  | isI1 info =
      case (\(I1 x) -> x) info of
        A -> putStr "" -- nothing is printed
        B -> mapM_ putStrLn [show . lastFrom3 $ uni]
        C -> mapM_ putStrLn [show . firstFrom3 $ uni]
        D -> mapM_ putStrLn [show . secondFrom3 $ uni]
        E -> mapM_ putStrLn [show . lastFrom3 $ uni, show . firstFrom3 $ uni]
        F -> mapM_ putStrLn [show . lastFrom3 $ uni, show . secondFrom3 $ uni]
        G -> mapM_ putStrLn [show . firstFrom3 $ uni, show . secondFrom3 $ uni]
        _ -> mapM_ putStrLn [show . lastFrom3 $ uni, show . firstFrom3 $ uni, show. secondFrom3 $ uni]  -- the most verbose output
  | otherwise =
      case (\(I2 x) -> x) info of
        Af _ -> putStr "" -- nothing is printed
        Bf xs -> toFile xs [show . lastFrom3 $ uni]
        Cf xs -> toFile xs [show . firstFrom3 $ uni]
        Df xs -> toFile xs [show . secondFrom3 $ uni]
        Ef xs -> toFile xs [show . lastFrom3 $ uni, show . firstFrom3 $ uni]
        Ff xs -> toFile xs [show . lastFrom3 $ uni, show . secondFrom3 $ uni]
        Gf xs -> toFile xs [show . firstFrom3 $ uni, show . secondFrom3 $ uni]
        ~(Hf xs) -> toFile xs [show . lastFrom3 $ uni, show . firstFrom3 $ uni, show. secondFrom3 $ uni]  -- the most verbose output

-- | Is used to print output specified to the 'stdout' or to the 'FilePath' specified as the inner argument in the 'Info2' parameter.
printUniquenessG1List
  :: (Show (t a), Show b, Show (t2 b)) => Info2 -- ^ A parameter to control the predefined behaviour of the printing. The 'I1' branch prints to the 'stdout' and the 'I2' - to the file.
  -> [UniquenessG1T2 t t2 a b] -- ^ The list of elements, for which the information is printed.
  -> IO ()
printUniquenessG1List info (y:ys)
  | isI1 info =
      case (\(I1 x) -> x) info of
        A -> putStr "" -- nothing is printed
        B -> mapM_ putStrLn . map (show . lastFrom3) $ (y:ys)
        C -> mapM_ putStrLn . map (show . firstFrom3) $ (y:ys)
        D -> mapM_ putStrLn . map (show . secondFrom3) $ (y:ys)
        E -> (putStrLn . show . lastFrom3 $ y) >> (putStrLn . show . firstFrom3 $ y) >> printUniquenessG1List info ys
        F -> (putStrLn . show . lastFrom3 $ y) >> (putStrLn . show . secondFrom3 $ y) >> printUniquenessG1List info ys
        G -> (putStrLn . show . firstFrom3 $ y) >> (putStrLn . show . secondFrom3 $ y) >> printUniquenessG1List info ys
        _ -> (putStrLn . show . lastFrom3 $ y) >> (putStrLn . show . firstFrom3 $ y) >> (putStrLn . show. secondFrom3 $ y) >> printUniquenessG1List info ys  -- the most verbose output
  | otherwise =
      case (\(I2 x) -> x) info of
        Af _ -> putStr "" -- nothing is printed
        Bf xs -> toFile xs . map (show . lastFrom3) $ (y:ys)
        Cf xs -> toFile xs . map (show . firstFrom3) $ (y:ys)
        Df xs -> toFile xs . map (show . secondFrom3) $ (y:ys)
        Ef xs -> toFile xs . map (\t -> (show (lastFrom3 t) ++ newLineEnding ++ show (firstFrom3 t))) $ ys
        Ff xs -> toFile xs . map (\t -> (show (lastFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ ys
        Gf xs -> toFile xs . map (\t -> (show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ ys
        ~(Hf xs) -> toFile xs . map (\t -> (show (lastFrom3 t) ++ newLineEnding ++ show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ ys  -- the most verbose output
printUniquenessG1List _ _ = return ()

-- | A variant of the 'printUniquenessG1List' where @a@ is 'Char' so that the inner third arguments in the triples are 'String's.
printUniquenessG1ListStr
  :: (Show b, Show (t2 b)) => Info2 -- ^ A parameter to control the predefined behaviour of the printing. The 'I1' branch prints to the 'stdout' and the 'I2' - to the file.
  -> VB.Vector (UniquenessG1T2 [] t2 Char b) -- ^ The 'VB.Vector' of elements, for which the information is printed.
  -> IO ()
printUniquenessG1ListStr info v
  | VB.null v = return ()
  | isI1 info =
      case (\(I1 x) -> x) info of
        A -> putStr "" -- nothing is printed
        B -> VB.mapM_ putStrLn . VB.map lastFrom3 $ v
        C -> VB.mapM_ putStrLn . VB.map (show . firstFrom3) $ v
        D -> VB.mapM_ putStrLn . VB.map (show . secondFrom3) $ v
        E -> (putStrLn . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1ListStr info (VB.unsafeTail v)
        F -> (putStrLn . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1ListStr info (VB.unsafeTail v)
        G -> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1ListStr info (VB.unsafeTail v)
        _ -> (putStrLn . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show. secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1ListStr info (VB.unsafeTail v)  -- the most verbose output
  | otherwise =
      case (\(I2 x) -> x) info of
        Af _ -> putStr "" -- nothing is printed
        Bf xs -> toFile xs . VB.toList . VB.map lastFrom3 $ v
        Cf xs -> toFile xs . VB.toList . VB.map (show . firstFrom3) $ v
        Df xs -> toFile xs . VB.toList . VB.map (show . secondFrom3) $ v
        Ef xs -> toFile xs . VB.toList . VB.map (\t -> (lastFrom3 t ++ newLineEnding ++ show (firstFrom3 t))) $ v
        Ff xs -> toFile xs . VB.toList . VB.map (\t -> (lastFrom3 t ++ newLineEnding ++ show (secondFrom3 t))) $ v
        Gf xs -> toFile xs . VB.toList . VB.map (\t -> (show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ v
        ~(Hf xs) -> toFile xs . VB.toList . VB.map (\t -> (lastFrom3 t ++ newLineEnding ++ show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ v  -- the most verbose output

-- | A variant of the 'printUniquenessG1List' where @a@ is 'Char' so that the inner third arguments in the triples are 'VB.Vector' of 'Char'.
printUniquenessG1VChar
  :: (Show b, Show (t2 b)) => Info2 -- ^ A parameter to control the predefined behaviour of the printing. The 'I1' branch prints to the 'stdout' and the 'I2' - to the file.
  -> VB.Vector (UniquenessG1T2 VB.Vector t2 Char b) -- ^ The 'VB.Vector' of elements, for which the information is printed.
  -> IO ()
printUniquenessG1VChar info v
  | VB.null v = return ()
  | isI1 info =
      case (\(I1 x) -> x) info of
        A -> putStr "" -- nothing is printed
        B -> VB.mapM_ (putStrLn . VB.toList) . VB.map lastFrom3 $ v
        C -> VB.mapM_ putStrLn . VB.map (show . firstFrom3) $ v
        D -> VB.mapM_ putStrLn . VB.map (show . secondFrom3) $ v
        E -> (putStrLn . VB.toList . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1VChar info (VB.unsafeTail v)
        F -> (putStrLn . VB.toList . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1VChar info (VB.unsafeTail v)
        G -> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1VChar info (VB.unsafeTail v)
        _ -> (putStrLn . VB.toList . lastFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show . firstFrom3 . VB.unsafeIndex v $ 0) >> (putStrLn . show. secondFrom3 . VB.unsafeIndex v $ 0) >> printUniquenessG1VChar info (VB.unsafeTail v)  -- the most verbose output
  | otherwise =
      case (\(I2 x) -> x) info of
        Af _ -> putStr "" -- nothing is printed
        Bf xs -> toFile xs . VB.toList . VB.map (VB.toList . lastFrom3) $ v
        Cf xs -> toFile xs . VB.toList . VB.map (show . firstFrom3) $ v
        Df xs -> toFile xs . VB.toList . VB.map (show . secondFrom3) $ v
        Ef xs -> toFile xs . VB.toList . VB.map (\t -> (VB.toList (lastFrom3 t) ++ newLineEnding ++ show (firstFrom3 t))) $ v
        Ff xs -> toFile xs . VB.toList . VB.map (\t -> (VB.toList (lastFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ v
        Gf xs -> toFile xs . VB.toList . VB.map (\t -> (show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ v
        ~(Hf xs) -> toFile xs . VB.toList . VB.map (\t -> (VB.toList (lastFrom3 t) ++ newLineEnding ++ show (firstFrom3 t) ++ newLineEnding ++ show (secondFrom3 t))) $ v  -- the most verbose output

-- | Auxiliary printing function to define the line ending in some cases.
newLineEnding :: String
newLineEnding
  | nativeNewline == LF = "\n"
  | otherwise = "\r\n"

-- | Variant of the 'maximumElBy' function where all the given \"properties\" are used.
-- The predefined library \"properties\" or related to them functions can be found in the package @uniqueness-periods-vector-properties@.
maximumElByAll ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  ->  UniqG2T2 t t2 a b -- ^ The data to be analyzed.
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
         maximumElBy (k - 1) (VB.unsafeSlice 0 (k - 1) vN) (UL2 (VB.empty,vK))
 | otherwise = VB.maximumBy (\(_,vN0,_) (_,vN1,_) -> compare (VB.unsafeIndex vN0 0) (VB.unsafeIndex vN1 0)) . uniquenessVariantsGN hd whspss f1 f2 f3 perms rr vN frep $ v

-- | A variant for 'uniquenessVariants2GNB' and 'uniquenessVariants2GNPB' with the second argument defining, which one is used.
uniquenessVariantsGN ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => a -- ^ The first from the left element inthe \"whitespace symbols\" 'Foldable' structure.
  -> t a -- ^ A list of \"whitespace symbols\" that delimits the subGs in the structure to be processed.
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> PreApp t a -- ^ A parameter to specify the lists to be prepended and postpended to the given data to be processed before actual processment.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t a -- ^ The data to be processed.
  -> VB.Vector (UniquenessG1T2 t t2 a b)
uniquenessVariantsGN hd whspss f1 f2 f3 perms (PA ts us) vN frep data1 = uniquenessVariants2GNPB ts us hd f1 f2 f3 perms vN frep (subG whspss data1)
uniquenessVariantsGN hd whspss f1 f2 f3 perms K vN frep data1 = uniquenessVariants2GNB hd f1 f2 f3 perms vN frep (subG whspss data1)
{-# INLINE uniquenessVariantsGN #-}

-- | Rearranges the last argument.
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
  -> UniqG2T2 t t2 a b -- ^ The data to be analyzed.
  -> UniqG2T2 t t2 a b
maximumElByVec k vN x
 | VB.null . snd . get22 $ x = x
 | otherwise = let !uniq = maximumElBy k vN x in let !snD = secondFrom3 uniq in UL2 ((\(!v1,!v2) -> ((fst . get22 $ x) `mappend` v1,v2)) .
      VB.unstablePartition (equalSnDs snD . secondFrom3) . snd . get22 $ x)
{-# NOINLINE maximumElByVec #-}

equalSnDs
  :: Ord b => VB.Vector b
  -> VB.Vector b
  -> Bool
equalSnDs v1 v2
 | VB.null v1 = VB.null v2
 | VB.null v2 = False
 | VB.unsafeIndex v1 0 == VB.unsafeIndex v2 0 = equalSnDs (VB.unsafeSlice 1 (VB.length v1 - 1) v1) (VB.unsafeSlice 1 (VB.length v2 - 1) v2)
 | otherwise = False

-- | A variant of the 'maximumElByVec' where all the given \"properties\" are used.
maximumElByVecAll ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> UniqG2T2 t t2 a b -- ^ The data to be analyzed.
  -> UniqG2T2 t t2 a b
maximumElByVecAll vN = maximumElByVec (VB.length vN) vN
{-# INLINE maximumElByVecAll #-}

-- |  Finds out the @n@ (the first 'Int' argument) consequential maximum elements, and then rearranges the input moving the elements equal by the first element
-- in the triple to the maximum element to the first element in the tuple.
uniqNPropertiesN ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => Int -- ^ A quantity of the recursive calls that returns each one a new resulting group from the rest of the data processed.
  -> Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> UniqG2T2 t t2 a b -- ^ The data to be analyzed.
  -> UniqG2T2 t t2 a b
uniqNPropertiesN n k vN y
 | n <= 0 = y
 | otherwise = uniqNPropertiesN (n - 1) k vN . maximumElByVec k vN $ y
{-# NOINLINE uniqNPropertiesN #-}

-- | A variant of the 'uniqNPropertiesN' where all the given \"properties\" are used.
uniqNPropertiesNAll ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, Ord b, Show a, Show b) => Int -- ^ A quantity of the recursive calls that returns each one a new resulting group from the rest of the data processed.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> UniqG2T2 t t2 a b -- ^ The data to be analyzed.
  -> UniqG2T2 t t2 a b
uniqNPropertiesNAll n vN = uniqNPropertiesN n (VB.length vN) vN
{-# INLINE uniqNPropertiesNAll #-}

--------------------------------------------------------------------------------------------

-- | The full analyzing and processment function.
uniqNProperties2GN ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Foldable t2, UGG1 t (PreApp t a) a, Ord b, Show a, Show b) => a -- ^ The first most common element in the whitespace symbols structure
  -> t a -- ^ A list of \"whitespace symbols\" that delimits the sublists in the list to be processed.
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> PreApp t a -- ^ A parameter to specify the lists to be prepended and postpended to the given data to be processed before actual processment.
  -> Int -- ^ A quantity of the recursive calls that returns each one a new resulting group from the rest of the data processed.
  -> Int -- ^ The quantity of the represented as functions \"properties\" to be applied from the second argument. The order is from the right to the left.
  -> VB.Vector (t2 b -> b) -- ^ 'VB.Vector' of the represented as functions \"properties\" to be applied consequently.
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t a -- ^ The data to be processed.
  -> UniqG2T2 t t2 a b
uniqNProperties2GN hd whspss f1 f2 f3 perms rr n k vN frep v
 | n <= 0 = UL2 (VB.empty,VB.empty)
 | otherwise = let v1 = uniquenessVariants2GNPB (get1m rr) (get2m rr) hd f1 f2 f3 perms vN frep (subG whspss v) in uniqNPropertiesN (n - 1) k vN . maximumElByVec k vN $ (UL2 (VB.empty,v1))
