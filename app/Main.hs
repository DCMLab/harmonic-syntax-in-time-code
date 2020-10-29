-- {-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Main 
    ( Grammar(..)
    , parse
    , evalModel
    , main
    , foo
    , writeIsmirData
    ) where

import ParseTree
import PitchClassSymbol

import Data.Ratio
import Data.Maybe (catMaybes)
import Data.Array
import Data.List.Split (splitOn)
import Data.Monoid ((<>))
import Data.Semiring hiding (Matrix)
import Data.NumInstances
import Data.Either (partitionEithers)
import System.Random
import Control.Monad ((>=>))
import Control.Monad.Random hiding (RandT)
import Control.Monad.Trans.State
import Control.Monad.ST
import Control.Arrow ((&&&))
import Math.Probable
import Math.Probable.Distribution
import Numeric.Log (Log(..), ln, Precise)
import Numeric.SpecFunctions (digamma)

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWCD
import qualified Data.List as L
import qualified Data.Text as T
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Monoid as Mon

import qualified Numeric.Log as LL
logDomainSum :: (RealFloat a, Precise a, Foldable f) => f (Log a) -> Log a
logDomainSum = LL.sum

instance Random (Log Double) where
    random g = (Exp . log $ a, g') where
        (a, g') = random g
    randomR (lo,hi) g = (Exp . log $ a, g') where
        (a, g') = randomR (exp . ln $ lo, exp . ln $ hi) g

--------------------
--- Random Monad ---
--------------------

type RandIO a = RandT IO a

dirichlet :: [Double] -> RandIO [Double]
dirichlet = RandT . MWCD.dirichlet 

--------------------------------
--- Variational Distribution ---
--------------------------------

data VarDist a c = VarDist { support    :: [a]
                           , priorcount :: a -> c
                           , logprob    :: a -> Log Double
                           , varprob    :: a -> Log Double
                           }

setObservations :: VarDist a Double -> (a -> Double) -> VarDist a Double
setObservations d counts = d { logprob = Exp . log . (/countsum) . posteriorcounts
                             , varprob = (/varsum) . Exp . digamma . posteriorcounts
                             }
    where posteriorcounts a = priorcount d a + counts a
          countsum = sum . map posteriorcounts . support $ d
          varsum   = logDomainSum . map (Exp . digamma . posteriorcounts) . support $ d

sampleVarDist :: Ord a => [(a,Double)] -> RandIO (VarDist a Double)
sampleVarDist priorcounts = do 
    ps <- dirichlet cs 
    let logprobs = M.fromList . zip as . map (Exp . log) $ ps
    return $ VarDist as ((M.fromList priorcounts) M.!) (logprobs M.!) (logprobs M.!) 
    where as = fst <$> priorcounts
          cs = snd <$> priorcounts

categoricalWithCounts :: Ord a => [(a,Double)] -> VarDist a Double
categoricalWithCounts acs = VarDist as priorcount logprob logprob where 
    s  = sum . map snd $ acs
    as = map fst . filter ( (>0) . snd ) $ acs
    priorcounts = M.fromList $ acs
    priorcount a = case M.lookup a priorcounts of
        Just c  -> c
        Nothing -> 0
    logprobs = M.fromList . (map . fmap) (Exp . log . (/s)) $ acs
    logprob a = case M.lookup a logprobs of
        Just p  -> p
        Nothing -> 0

uniformCategorical :: Ord a => [a] -> VarDist a Double
uniformCategorical as = categoricalWithCounts . zip as . replicate (length as) $ 1

productVarDist :: VarDist a c -> VarDist b c -> VarDist (a,b) (c,c)
productVarDist da db = VarDist { support    = [ (a,b) | a <- support da, b <- support db ]
                               , priorcount = \(a,b) -> (priorcount da a, priorcount db b)
                               , logprob    = \(a,b) -> logprob da a * logprob db b
                               , varprob    = \(a,b) -> varprob da a * varprob db b
                               }

---------------
--- Grammar ---
---------------

data Grammar r = Grammar { start    :: Symbol r
                         , rules    :: [r]
                         , ruleDist :: Symbol r -> VarDist r (Count r)
                         }

productGrammar :: (Double ~ Count r1, Double ~ Count r2) 
               => Grammar r1 -> Grammar r2 -> Grammar (r1, r2)
productGrammar (Grammar s1 rs1 d1) (Grammar s2 rs2 d2) =
    Grammar { start = (s1,s2)
            , rules = [ (r1, r2) | r1 <- rs1, r2 <- rs2 ]
            , ruleDist = \(a,b) -> productVarDist (d1 a) (d2 b)
            }

ruleProb :: Grammar r -> Symbol r -> r -> Log Double
ruleProb grammar a = logprob (ruleDist grammar a)

------------
--- Rule ---
------------

class (Ord r) => Rule r where
    type Symbol r
    type Count r
    apply  :: r -> Symbol r -> Maybe [Symbol r]
    arity  :: r -> Int
    invert :: r -> [Symbol r] -> Maybe (Symbol r)

type RuleSym r a = (Rule r, a ~ Symbol r, Ord a)

collectionStep :: (RuleSym r a) => [r] -> [a] -> [a]
collectionStep rules as = L.union as as' where
    as' = foldl L.union [] (catMaybes $ apply <$> rules <*> as)

collectSymbols :: (RuleSym r a) => [r] -> [a] -> [a]
collectSymbols rules as
    | as == as' = as
    | otherwise = collectSymbols rules as'
    where as' = collectionStep rules as

instance (Rule r1, Rule r2) => Rule (r1,r2) where
    type Symbol (r1, r2) = (Symbol r1, Symbol r2)
    type Count  (r1, r2) = (Double, Double)
    apply (r1, r2) (a1, a2) = case (apply r1 a1, apply r2 a2) of
        (Nothing  , _        ) -> Nothing
        (_        , Nothing  ) -> Nothing
        (Just rhs1, Just rhs2) -> Just . zip rhs1 $ rhs2
    arity (r1,r2) 
        | arity r1 == arity r2 = arity r1
        | otherwise = error "product of two rules only defined for equal arity"
    invert (r1,r2) rhs = case (invert r1 . map fst $ rhs, invert r2 . map snd $ rhs) of
        (Nothing  , _        ) -> Nothing
        (_        , Nothing  ) -> Nothing
        (Just lhs1, Just lhs2) -> Just (lhs1, lhs2)

---------------
--- CFGRule ---
---------------

data CFGRule a = UnaryRule a a | BinaryRule a a a
    deriving (Eq, Ord)

instance Show a => Show (CFGRule a) where
    show (UnaryRule lhs rhs) = 
        show lhs <> " --> " <> show rhs
    show (BinaryRule lhs rhs1 rhs2) = 
        show lhs <> " --> " <> show rhs1 <> " " <> show rhs2

instance (Ord a) => Rule (CFGRule a) where
    type Symbol (CFGRule a) = a
    type Count  (CFGRule a) = Double
    apply (UnaryRule lhs rhs) a
        | lhs == a  = Just [rhs]
        | otherwise = Nothing
    apply (BinaryRule lhs rhs1 rhs2) a
        | lhs == a  = Just [rhs1, rhs2]
        | otherwise = Nothing
    arity (UnaryRule  _ _  ) = 1
    arity (BinaryRule _ _ _) = 2
    invert (UnaryRule lhs rhs) [a]
        | rhs == a = Just lhs
        | otherwise = Nothing
    invert (BinaryRule lhs rhs1 rhs2) [a1,a2]
        | rhs1 == a1 && rhs2 == a2 = Just lhs
        | otherwise = Nothing
    invert _ _ = Nothing

treebankGrammar :: (Ord a) => a -> [a] -> [FullTree a] -> Grammar (CFGRule a)
treebankGrammar start chords trees = Grammar start rules dist where
    treebankRuleCounts = ruleCountsFromBranches (trees >>= treeBranches)
    ruleCounts = M.unionsWith (+) [ startRuleCounts chords
                                  , binaryRuleCounts chords
                                  , treebankRuleCounts
                                  ]
    rules = M.keys ruleCounts
    dist sym = categoricalWithCounts [ (rule, ruleCounts M.! rule) 
                                     | rule <- rules
                                     , apply rule sym /= Nothing 
                                     ]
                                     
    ruleCountsFromBranches branches = M.fromListWith (+) rules where 
        rules = [ (BinaryRule a b c, 1) | [a,b,c] <- branches ]

    startRuleCounts chords = M.fromList [ (UnaryRule start a, 1) | a <- chords ] 

    binaryRuleCounts chords = M.union rightHeadedRules leftHeadedRules where
        rightHeadedRules = M.fromList [ (BinaryRule a b a, 0.01) 
                                    | a <- chords
                                    , b <- chords 
                                    ]
        leftHeadedRules  = M.fromList [ (BinaryRule a a b, 0.01) 
                                    | a <- chords
                                    , b <- chords 
                                    ]

------------------
--- PebbleRule ---
------------------

data PebbleRule = UnaryPebbleRule | BinaryPebbleRule Rational
    deriving (Eq, Ord, Show)

instance Rule PebbleRule where
    type Symbol PebbleRule = Rational
    type Count  PebbleRule = Double
    apply UnaryPebbleRule          a = Just [a]
    apply (BinaryPebbleRule ratio) a 
        | denominator left <= 136 && denominator right <= 136 = Just [left, right]
        | otherwise = Nothing 
        where left  = ratio * a
              right = a - left
    arity UnaryPebbleRule = 1
    arity (BinaryPebbleRule _) = 2
    invert UnaryPebbleRule [a] = Just a
    invert (BinaryPebbleRule ratio) [left, right]
        | left / s == ratio = Just s
        | otherwise = Nothing
        where s = left + right
    invert _ _ = Nothing

pebbleGrammarFromSplitCounts :: M.Map Rational Int -> Grammar PebbleRule
pebbleGrammarFromSplitCounts splitCounts = Grammar 1 rules dist where
    allRules   = M.fromList [ (BinaryPebbleRule (n % d), 0.01) | d <- [2..68], n <- [1..(d-1)] ]
    ruleCounts = M.insert UnaryPebbleRule 1 
               . M.map fromIntegral 
               . M.mapKeys BinaryPebbleRule 
               $ splitCounts
    rules      = M.keys ruleCounts
    dist       = const 
               . categoricalWithCounts 
               . M.assocs 
               . M.unionWith (+) ruleCounts
               $ allRules

--------------
--- Parser ---
--------------

class Parser p where
    type Category p
    type Score p
    goal        :: p -> Category p
    completions :: p -> [Category p] -> [(Category p, Score p)]

type ParserSymScore p a s = (Parser p, a ~ Category p, Ord a, s ~ Score p, SemiringScore s)

type Chart sym s = Array (Int, Int) (M.Map sym s)

mkChart :: Int -> (Int -> Int -> M.Map sym s) -> Chart sym s
mkChart n f = array ((0,0), (n-1,n-1)) [ ((i,j), f i j) | i <- [0..n-1], j <- [0..n-1] ]

chart :: (ParserSymScore p a s) => p -> (Int -> Int -> Bool) -> [a] -> Chart a s
chart p isAllowedSpan syms =
    let n     = length syms
        chart = mkChart n f
        f i j = addUnaryCompletions $ case compare i j of
            GT -> M.empty
            EQ -> M.singleton (syms !! i) terminalScore
            LT -> M.fromListWith (<+>) 
                [ (lhs, s <.> s1 <.> s2)
                | k <- [0..j-1]
                , isAllowedSpan i k && isAllowedSpan (k+1) j
                , (rhs1, s1) <- M.assocs $ chart ! (i  , k) 
                , (rhs2, s2) <- M.assocs $ chart ! (k+1, j)
                , (lhs,  s ) <- completions p [rhs1, rhs2]
                ]
    in chart
    where addUnaryCompletions comps = M.unionWith (<+>) comps (ucomps comps)
          ucomps comps = M.fromListWith (<+>) [ (lhs, s' <.> s)
                                              | (rhs, s ) <- M.assocs comps
                                              , (lhs, s') <- completions p [rhs]
                                              ]

parse :: (ParserSymScore p a s) => p -> [a] -> s
parse p syms = spanConditionedParse p everySpanAllowed syms where
    everySpanAllowed _ _ = True

spanConditionedParse :: (ParserSymScore p a s) => p -> (Int -> Int -> Bool) -> [a] -> s
spanConditionedParse p f syms = case M.lookup (goal p) heads of
    Just s  -> s
    Nothing -> zero
    where heads = chart p f syms ! (0, length syms - 1)

spanConditionsFromTree :: FullTree a -> Int -> Int -> Bool
spanConditionsFromTree tree i j = S.member (i,j) allSpans where
    n = length . leafValues $ tree
    leafSpans = [ (i,i) | i <- [0..n-1] ]
    allSpans = S.fromList
             . (leafSpans ++) 
             . constituentSpans 
             . forgetLeafLabels 
             $ tree

estimateValueCounts :: ( ParserSymScore p a s, s ~ ScoredForest s' b
                       , Random s', Ord s', Semiring s', Ord b, RandomGen g
                       ) 
                    => p -> (Int -> Int -> Bool) -> [a] -> Rand g (M.Map b Double)
estimateValueCounts p isAllowedSpan as = do
    bs <- joinRandomTreeValues numSamples forest
    return . fmap (/ fromIntegral numSamples) . M.fromListWith (+) . zip bs $ repeat 1
    where forest = spanConditionedParse p isAllowedSpan as
          n = length as
          numSamples = n * n

----------------------
--- Product Parser ---
----------------------

data ProductParser s p1 p2 where 
    ProductParser :: ( Parser p1,           s1 ~ Score p1
                     , Parser p2,           s2 ~ Score p2
                     , CombineScores s1 s2, s  ~ ResultScore s1 s2 )
                  => p1 -> p2 -> ProductParser s p1 p2

instance Parser (ProductParser s p1 p2) where
    type Category (ProductParser s p1 p2) = (Category p1, Category p2)
    type Score    (ProductParser s p1 p2) = s
    goal (ProductParser p1 p2) = (goal p1, goal p2)
    completions (ProductParser p1 p2) rhs = do 
        (lhs1, s1) <- comps1
        (lhs2, s2) <- comps2
        return ( (lhs1, lhs2), combineScores s1 s2 )
        where comps1 = completions p1 . (map fst) $ rhs
              comps2 = completions p2 . (map snd) $ rhs

---------------------
--- Pebble Parser ---
---------------------

newtype PebbleParser s = PebbleParser (M.Map Rational s)

instance Semiring s => Parser (PebbleParser s) where
    type Category (PebbleParser s) = Rational
    type Score    (PebbleParser s) = s
    goal _ = 1 % 1
    completions (PebbleParser scores) [child]      = [(child, scores M.! 1)]
    completions (PebbleParser scores) [left,right] = case scores M.!? ( left / (left+right) ) of
        Just s  -> [(left+right, s)]
        Nothing -> []

mkPebbleParser :: M.Map Rational Int ->  PebbleParser (ScoredForest BestLogProb Rational)
mkPebbleParser splitCounts = PebbleParser scores where
    ratios = M.unionWith (+) (fmap fromIntegral splitCounts) 
           . M.insertWith (+) 1 80 
           . M.fromList 
           $ [ (n % d, 0.01) | d <- [2..68], n <- [1..d-1] ]
    dist   = categoricalWithCounts 
           . M.assocs 
           $ ratios
    scores = M.fromList [ (r, Value (Best . logprob dist $ r) r) | r <- M.keys ratios ]

mkPebbleSampleParser :: PebbleParser (ScoredForest (Log Double) Rational)
mkPebbleSampleParser = PebbleParser scores where
    ratios = L.nub $ (1, 0.01) : [ (n % d, 0.01) | d <- [2..68], n <- [1..d-1] ]
    scores = M.fromList [ (r, Value (logprob dist r) r) | r <- map fst ratios ]
    dist = categoricalWithCounts ratios

---------------------
--- Rhythm Parser ---
---------------------

data RhythmCategory = RCat Rational Rational
    deriving (Eq, Ord, Show)

data RhythmRule = UnaryRhythmRule | UpBeatSplit Rational | DownBeatSplit Rational Rational
    deriving (Eq, Ord, Show)

data RhythmParser s = RhythmParser { downbeatDist :: VarDist RhythmRule Double -- upbeat == 0
                                   , upbeatDist   :: VarDist RhythmRule Double -- upbeat /= 0
                                   , rhythmScores :: M.Map (Bool, RhythmRule) s
                                   }

instance Parser (RhythmParser s) where
    type Category (RhythmParser s) = RhythmCategory
    type Score    (RhythmParser s) = s
    goal _ = RCat 0 1
    completions (RhythmParser _ _ scores) rhs = catMaybes $
        [upbeatSplitComps, downbeatSplitComps, unaryComps] <*> pure scores <*> pure rhs where

        upbeatSplitComps :: M.Map (Bool, RhythmRule) s
                         -> [RhythmCategory] -> Maybe (RhythmCategory,s)
        upbeatSplitComps scores [RCat up1 down1, RCat up2 down2]
            | up1 <= down1 && up2 == 0 = (\s -> (c,s)) <$> scores M.!? (False, r)
            | otherwise = Nothing
            where c = RCat (up1 + down1) down2
                  u = down1 / (up1 + down1)
                  r = UpBeatSplit u
        upbeatSplitComps _ _ = Nothing

        downbeatSplitComps :: M.Map (Bool, RhythmRule) s
                           -> [RhythmCategory] -> Maybe (RhythmCategory,s)
        downbeatSplitComps scores [RCat up1 down1, RCat up2 down2]
            | up2 <= down2 = (\s -> (c,s)) <$> scores M.!? (up1 == 0, r)
            | otherwise = Nothing
            where c = RCat up1 (down1 + up2 + down2) 
                  v = up2 / down2
                  w = down2 / (down1 + up2 + down2)
                  r = DownBeatSplit v w
        downbeatSplitComps _ _ = Nothing

        unaryComps :: M.Map (Bool, RhythmRule) s
                   -> [RhythmCategory] -> Maybe (RhythmCategory,s)
        unaryComps scores [c@(RCat up _)] = (\s -> (c,s)) <$> scores M.!? (up == 0, UnaryRhythmRule)
        unaryComps _ _ = Nothing

calkinWilfTree :: Rational -> FullTree Rational
calkinWilfTree root = FT root [calkinWilfTree (n % (n+d)), calkinWilfTree ((n+d) % d)] where
    n = numerator   root
    d = denominator root

calkinWilfRationals :: [Rational]
calkinWilfRationals = breadthFirstSequence . calkinWilfTree $ 1

calkinWilfProperRationals :: [Rational]
calkinWilfProperRationals = filter (<1) calkinWilfRationals

breadthFirstSequence :: FullTree a -> [a]
breadthFirstSequence tree = values [tree] where
    values [] = []
    values ts = map headValue ts ++ (values . concatMap children $ ts) where 
        children (FT _ ts) = ts

mkRhythmSampleParser :: RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule))
mkRhythmSampleParser = RhythmParser downbeatDist upbeatDist rhythmScores where
    ratios         = take 100 calkinWilfProperRationals
    -- ratios         = L.nub [ n % d | d <- [2..68], n <- [1..d-1] ]
    downbeatSplits = DownBeatSplit <$> 0 : ratios <*> ratios
    upbeatSplits   = UpBeatSplit   <$> filter (1%2 <) (1:ratios)
    downbeatDist   = uniformCategorical 
                   . (UnaryRhythmRule :)
                   $ downbeatSplits 
    upbeatDist     = uniformCategorical 
                   . (UnaryRhythmRule :) 
                   $ downbeatSplits ++ upbeatSplits
    rhythmScores   = M.fromList $ do
        upbeatZero <- [True, False]
        let dist = if upbeatZero then downbeatDist else upbeatDist
        r <- support dist
        let p = varprob dist r 
        guard (p /= 0)
        return ((upbeatZero, r), Value p (upbeatZero, r))

    -- rhythmScore c@(RCat up down) r = if p /= 0 then Just (Value p (c,r)) else Nothing 
    --     where p = logprob dist r
    --           dist = if up == 0 then downbeatDist else upbeatDist
    -- rhythmScore c r = Just (Value 1 (c,r))

rhythmBestParser :: RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule))
                 -> RhythmParser (ScoredForest BestLogProb ())
rhythmBestParser (RhythmParser downbeatDist upbeatDist rhythmScores) =
    RhythmParser downbeatDist upbeatDist rhythmScores' where 
        rhythmScores' = M.fromList $ do
            upbeatZero <- [True, False]
            let dist = if upbeatZero then downbeatDist else upbeatDist
            r <- support dist
            let p = logprob dist r 
            guard (p /= 0)
            return ((upbeatZero, r), Value (Best p) ()) 

improveRhythmParser :: (RandomGen g)
                    => [IRealTune]
                    -> RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule))
                    -> Rand g (RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule)))
improveRhythmParser tunes p = updateRhythmParser p <$> estimateValueCountsFromTunes p tunes

updateRhythmParser :: RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule))
                   -> M.Map (Bool,RhythmRule) Double
                   -> RhythmParser (ScoredForest (Log Double) (Bool,RhythmRule))
updateRhythmParser p counts = RhythmParser downbeatDist' upbeatDist' rhythmScores' where
    (downbeatRewrites, upbeatRewrites) = partitionEithers . map classify . M.assocs $ counts
    classify ((upZero, r), c)
        | upZero    = Left  (r,c)
        | otherwise = Right (r,c)
    ruleCount rewrites r = case lookup r rewrites of
        Just c  -> c
        Nothing -> 0
    downbeatDist' = setObservations (downbeatDist p) (ruleCount downbeatRewrites)
    upbeatDist'   = setObservations (upbeatDist   p) (ruleCount upbeatRewrites  )
    rhythmScores' = M.fromList $ do
        upbeatZero <- [True, False]
        let dist = if upbeatZero then downbeatDist' else upbeatDist'
        r <- support dist
        let p = varprob dist r 
        guard (p /= 0)
        return ((upbeatZero, r), Value p (upbeatZero, r))

----------------------
--- Grammar Parser ---
----------------------

data GrammarParser a s = GrammarParser a ( M.Map [a] [(a,s)] )

mkGrammarParser :: (RuleSym r a) => (r -> a -> s) -> Grammar r -> GrammarParser a s
mkGrammarParser score g@(Grammar start rules _) =
    GrammarParser start (M.fromList [ (rhs, helper rhs) | rhs <- rhss ]) where
    rhss = catMaybes $ apply <$> rules <*> collectSymbols rules [start]
    helper rhs = catMaybes $ do
        r <- rules
        return $ do
            lhs <- invert r rhs
            return (lhs, score r lhs)

------------------
--- Map Parser ---
------------------

data MapParser a s = MapParser a ( M.Map [a] (M.Map a s) )

instance Ord a => Parser (MapParser a s) where
    type Category (MapParser a s) = a
    type Score    (MapParser a s) = s
    goal (MapParser g _) = g
    completions (MapParser _ c) as = case M.lookup as c of 
        Just comps -> M.assocs comps
        Nothing    -> []

mkMapParser :: (RuleSym r a, Semiring s) => (r -> a -> s) -> Grammar r -> MapParser a s
mkMapParser score g@(Grammar start rules _) = MapParser start comps where
    syms   = collectSymbols rules [start]
    lhss   = const id <$> rules <*> syms
    rhss   = apply    <$> rules <*> syms
    scores = score    <$> rules <*> syms
    comps  = M.fromListWith (M.unionWith (<+>)) 
           . catMaybes 
           $ zipWith3 transform rhss lhss scores
    transform Nothing    _   _ = Nothing
    transform (Just rhs) lhs s = Just (rhs, M.singleton lhs s)

instance (Ord a) => Parser (GrammarParser a s) where
    type Category (GrammarParser a s) = a
    type Score    (GrammarParser a s) = s
    goal (GrammarParser start _) = start
    completions (GrammarParser _ comps) rhs = case comps M.!? rhs of
        Just cs -> cs
        Nothing -> []

booleanParser :: (RuleSym r a) => Grammar r -> MapParser a Bool
booleanParser = mkMapParser $ \rule a -> if apply rule a == Nothing 
                                              then False 
                                              else True

countParser :: (RuleSym r a) => Grammar r -> MapParser a Int
countParser = mkMapParser $ \rule a -> if apply rule a == Nothing 
                                            then 0 
                                            else 1

insideParser :: (RuleSym r a) => Grammar r -> MapParser a (Log Double)
insideParser g = mkMapParser (\rule a -> ruleProb g a rule) g

forestParser :: (RuleSym r a) => Grammar r -> MapParser a (ScoredForest (Log Double) a)
forestParser g = mkMapParser (\rule a -> Value (ruleProb g a rule) a) g

viterbiForestParser :: (RuleSym r a) 
                    => Grammar r
                    -> MapParser a (ScoredForest BestLogProb a)
viterbiForestParser g = mkMapParser
    (\rule a -> Value (Best $ ruleProb g a rule) a) g

--------------------
--- Test Parsers ---
--------------------

gen = mkStdGen 42

data AnBnSym = S | A | AA | B | BB | X deriving (Eq, Ord, Show)

anbnParser :: MapParser AnBnSym Bool
anbnParser = booleanParser (Grammar S rs undefined) where
    rs = [ BinaryRule S A X
         , BinaryRule X S B
         , BinaryRule S A B 
         ]

anbnCNFParser :: MapParser AnBnSym (ScoredForest () AnBnSym)
anbnCNFParser = mkMapParser score (Grammar S rs undefined) where
    rs = [ BinaryRule S AA X
         , BinaryRule X S  BB
         , BinaryRule S AA BB
         , UnaryRule AA A
         , UnaryRule BB B
         ]
    score :: CFGRule AnBnSym -> AnBnSym -> ScoredForest () AnBnSym 
    score r a | apply r a == Nothing = Zero
              | otherwise            = Value () a

countTreesParser :: MapParser AnBnSym Int
countTreesParser = countParser (Grammar S rs undefined) where
    rs = [ BinaryRule S S S ]
    score :: CFGRule AnBnSym -> AnBnSym -> ScoredForest () AnBnSym 
    score r a | apply r a == Nothing = Zero
              | otherwise            = Value () a

allTreesParser :: MapParser AnBnSym (ScoredForest Int AnBnSym)
allTreesParser = mkMapParser score (Grammar S rs undefined) where
    rs = [ BinaryRule S S S ]
    score :: CFGRule AnBnSym -> AnBnSym -> ScoredForest Int AnBnSym 
    score r a | apply r a == Nothing = Zero
              | otherwise            = Value 1 a

allTreesForest :: Int -> ScoredForest Int AnBnSym
allTreesForest n = parse allTreesParser (take n (repeat S))

--------------
--- Scores ---
--------------

class Semiring s => SemiringScore s where
    terminalScore :: s
    terminalScore = one

instance Semiring s => SemiringScore (ScoredForest s v) where
    terminalScore = Terminal

instance SemiringScore Double
instance SemiringScore Bool
instance SemiringScore Int
instance (Precise s, RealFloat s) => SemiringScore (Log s)

------------------------------
--- Combinable Score Types ---
------------------------------

class (Semiring s1, Semiring s2) => CombineScores s1 s2 where
    type ResultScore s1 s2
    combineScores :: s1 -> s2 -> ResultScore s1 s2

instance CombineScores Double Double where
    type ResultScore Double Double = Double
    combineScores s1 s2 = s1 <.> s2

instance CombineScores (Log Double) (Log Double) where
    type ResultScore (Log Double) (Log Double) = Log Double
    combineScores s1 s2 = s1 <.> s2

instance CombineScores BestLogProb BestLogProb where
    type ResultScore BestLogProb BestLogProb = BestLogProb
    combineScores s1 s2 = s1 <.> s2

instance ( CombineScores s1 s2
         , Show v1
         , Show v2
         , Show s1
         , Show s2
         ) => CombineScores (ScoredForest s1 v1) (ScoredForest s2 v2) where
    type ResultScore (ScoredForest s1 v1) (ScoredForest s2 v2) = ScoredForest (ResultScore s1 s2) 
                                                                              (v1,v2)
    combineScores (Value s1 v1) (Value s2 v2) = Value (combineScores s1 s2) (v1,v2)
    combineScores f1 f2 = error $ show f1 ++ "\n" ++ show f2

------------------
--- BestScores ---
------------------

data BestLogProb = Best (Log Double) | NegInf deriving (Show, Eq)

unwrapBest :: BestLogProb -> Log Double
unwrapBest (Best p) = p
unwrapBest NegInf = Exp . log $ 0

instance Ord BestLogProb where
    NegInf <= _      = True
    Best p <= NegInf = False
    Best p <= Best q = p <= q

instance Semiring BestLogProb where
    Best p <+> Best q = Best (max p q)
    Best p <+> NegInf = Best p
    NegInf <+> Best q = Best q

    Best p <.> Best q = Best (p <.> q)
    _      <.> NegInf = NegInf
    NegInf <.> _      = NegInf

    zero = NegInf
    one  = Best (Exp 0)

instance SemiringScore BestLogProb

---------------------
--- ScoredForests ---
---------------------

data ScoredForest s v = Value s v
                      | Sum   s (ScoredForest s v) (ScoredForest s v) 
                      | Prod  s (ScoredForest s v) (ScoredForest s v) 
                      | Zero 
                      | One
                      | Terminal
                      deriving Show

score :: Semiring s => ScoredForest s v -> s
score (Value s _  ) = s
score (Sum   s _ _) = s
score (Prod  s _ _) = s
score Zero          = zero
score One           = one
score Terminal      = one

instance Semiring s => Semiring (ScoredForest s v) where
    zero = Zero
    one  = One

    f    <+> Zero = f
    Zero <+> f    = f
    f    <+> g    = Sum  (score f <+> score g) f g

    _    <.> Zero = Zero
    Zero <.> _    = Zero
    f    <.> One  = f
    One  <.> f    = f
    f    <.> g    = Prod (score f <.> score g) f g

-----------------------------------
--- ParseTree from ScoredForest ---
-----------------------------------

greedyBestTree :: (Semiring s, Ord s) => ScoredForest s a -> ParseTree a
greedyBestTree (Sum _ left right)
    | score left <= score right = greedyBestTree right
    | otherwise                 = greedyBestTree left
greedyBestTree (Prod _ (Prod _ (Value _ a) left) right) = 
    PT a (greedyBestTree left) [greedyBestTree right]
greedyBestTree (Prod _ (Value _ a) child) =
    PT a (greedyBestTree child) []
greedyBestTree _ = Leaf

allTrees :: Semiring s => ScoredForest s a-> [ParseTree a]
allTrees Terminal = [Leaf]
allTrees (Sum _ left right) = allTrees left ++ allTrees right
allTrees (Prod _ (Prod _ (Value _ a) left) right) = 
    PT a <$> allTrees left <*> (pure <$> allTrees right)
allTrees (Prod _ (Value _ a) child) =
    PT a <$> allTrees child <*> [[]]
allTrees _ = []

bernoulli :: (Semiring s, Ord s, Random s, RandomGen g) => s -> s -> Rand g Bool
bernoulli p q = do
    x <- liftRand $ randomR (zero, p <+> q)
    return (x < p)

randomTree :: (Semiring s, Ord s, Random s, RandomGen g) 
           => ScoredForest s a -> Rand g (ParseTree a)
randomTree (Sum _ left right) = do
    b <- bernoulli (score left) (score right)
    if b then randomTree left else randomTree right
randomTree (Prod _ (Prod _ (Value _ a) left) right) = 
    PT a <$> randomTree left <*> (pure <$> randomTree right)
randomTree (Prod _ (Value _ a) child) = 
    PT a <$> randomTree child <*> pure []
randomTree _ = return Leaf

randomTreeValues :: (Semiring s, Ord s, Random s, RandomGen g) 
                 => ScoredForest s v -> Rand g [v]
randomTreeValues = fmap (foldMap pure) . randomTree

joinRandomTreeValues :: (Semiring s, Ord s, Random s, RandomGen g) 
                     => Int -> ScoredForest s v -> Rand g [v]
joinRandomTreeValues n = fmap join . replicateM n . randomTreeValues

-----------------
--- Read data ---
-----------------

iRealPathPrefix = "treebank/"
iRealDataPath = iRealPathPrefix ++ "data.csv"
iRealMetaPath = iRealPathPrefix ++ "metadata.csv"

data IRealTune = IRealTune { tuneTitle     :: String
                           , tuneBPM       :: Int
                           , tuneMeasures  :: [Int]
                           , tuneBeats     :: [Int]
                           , tuneDurations :: [Int]
                           , tuneTree      :: FullTree String
                           , tuneChords    :: [String]
                           , tuneChordDurs :: [Rational]
                           }
    deriving (Show)

readIRealTunes :: IO [IRealTune]
readIRealTunes = transform <$> readBeatsPerMeasure <*> readFile iRealDataPath where
    transform bpm = intoTunes bpm
                  . fmap (takeWhile (/= ""))
                  . fmap (splitOn ";") 
                  . lines

    readBeatsPerMeasure :: IO (M.Map String Int)
    readBeatsPerMeasure = transform <$> readFile iRealMetaPath where
        transform = M.fromList
                . (map (\line -> (line !! 0, parseTimeSig $ line !! 3)))
                . tail
                . map (splitOn ";")
                . lines
        parseTimeSig "3/4" = 3
        parseTimeSig "4/4" = 4
        parseTimeSig "6/4" = 6

    intoTunes :: (M.Map String Int) -> [[String]] -> [IRealTune]
    intoTunes bpm [] = []
    intoTunes bpm lines = if tail (tuneLines !! 7) /= []
                          then intoTune bpm tuneLines : intoTunes bpm (drop 10 lines)
                          else intoTunes bpm (drop 10 lines) where 
        tuneLines = take 10 lines

    intoTune :: (M.Map String Int) -> [[String]] -> IRealTune
    intoTune bpm lines = IRealTune title
                                   measureDuration 
                                   measures 
                                   beats
                                   durations
                                   tree
                                   chords 
                                   chordDurs where
        title = head . tail $ lines !! 1
        measureDuration = bpm M.! title
        measures = map read . tail $ lines !! 2
        beats = map read . tail $ lines !! 3
        durations = calculateDurations measureDuration measures beats
        tree = parseTree . head . tail $ lines !! 7
        chords = leafValues . parseTree . head . tail $ lines !! 7
        chordDurations s [_] [] = [s]
        chordDurations _ [_] ds = [sum ds]
        chordDurations s (_:cs) (d:ds) = d : chordDurations s cs ds
        normalize as = (/s) . fromIntegral <$> as where
            s = fromIntegral . sum $ as
        chordDurs = normalize . chordDurations (sum durations) chords $ durations

    calculateDurations :: Int -> [Int] -> [Int] -> [Int]
    calculateDurations md _ [b] = [md + 1 - b]
    calculateDurations md (m1:m2:ms) (b1:b2:bs) = 
        d : calculateDurations md (m2:ms) (b2:bs) where
            d = if m1 == m2 then b2 - b1 else md + 1 - b1

readIRealTrees :: IO [FullTree String]
readIRealTrees = map tuneTree <$> readIRealTunes

leftSplitProportionCounts :: [IRealTune] -> M.Map Rational Int
leftSplitProportionCounts = M.fromListWith (+) 
                          . flip zip (repeat 1) 
                          . map ( \[a,b,c] -> b / a ) 
                          . allDurationBranches where
    allDurationBranches :: [IRealTune] -> [[Rational]]
    allDurationBranches = (=<<) $ uncurry durationBranches 
                                . ( forgetLeafLabels . tuneTree &&& tuneChordDurs )
    durationBranches :: (Num b) => ParseTree a -> [b] -> [[b]]
    durationBranches t = (map . map) Mon.getSum 
                    . treeBranches 
                    . labelAndCombineLeafs t 
                    . map Mon.Sum

writeLeftSplitProportions :: IO ()
writeLeftSplitProportions = writeFile "leftSplitProportions.csv" 
                          . unlines 
                          . map ( \(p,c) -> show p ++ "," ++ show c ) 
                          . rankedLeftSplitProportions 
                          =<< readIRealTunes where
    rankedLeftSplitProportions :: [IRealTune] -> [(Rational,Int)]
    rankedLeftSplitProportions = L.sortBy comp . M.assocs . leftSplitProportionCounts where
        comp (p1,c1) (p2,c2) = compare c2 c1

writeHarmonyRuleCounts :: IO ()
writeHarmonyRuleCounts = writeFile "harmonyRuleCounts.csv"
                       . unlines 
                       . map ( \(p,c) -> show p ++ ";" ++ show c ) 
                       . L.sortBy comp
                       . M.assocs
                       . M.fromListWith (+)
                       . map ( \branch -> (branch,1) )
                       . concatMap treeBranches
                       . map transposedTree
                       =<< readIRealTunes
    where comp (p1,c1) (p2,c2) = compare c2 c1

----------------------
--- String Symbols ---
----------------------

data StringSymbol = Start | Chord T.Text deriving (Eq, Ord)

instance Show StringSymbol where
    show Start = "START"
    show (Chord text) = T.unpack text

---------------------------
--- Model Construction  ---
---------------------------

type ModelParserCategory m p c = (p ~ ParserType m, Parser p, c ~ Category p)

class (Show m) => Model m where
    type ParserType m
    seqFromTune :: ModelParserCategory m p c => m -> IRealTune -> [c]
    trainParser :: ModelParserCategory m p c => m -> [c] -> [IRealTune] -> ParserType m

data HarmonyModel = HarmonyModel deriving Show

instance Model HarmonyModel where
    type ParserType HarmonyModel = MapParser StringSymbol 
                                             (ScoredForest BestLogProb StringSymbol)
    seqFromTune HarmonyModel = map (Chord . T.pack) . tuneChords
    trainParser HarmonyModel cs = viterbiForestParser 
                                . treebankGrammar Start cs 
                                . map (fmap (Chord . T.pack) . tuneTree)

data TransposedHarmonyModel = TransposedHarmonyModel deriving Show

instance Model TransposedHarmonyModel where
    type ParserType TransposedHarmonyModel = MapParser PitchClassSymbol 
                                                       (ScoredForest BestLogProb PitchClassSymbol)
    seqFromTune TransposedHarmonyModel = transposePCSymSeq 
                                       . map parsePCSym 
                                       . tuneChords
    trainParser TransposedHarmonyModel cs = viterbiForestParser 
                                          . treebankGrammar PCStart cs 
                                          . map transposedTree

transposedTree :: IRealTune -> FullTree PitchClassSymbol
transposedTree tune = fmap (transposePCSym (-root) . parsePCSym) . tuneTree $ tune where
    root = case last . map parsePCSym . tuneChords $ tune of
        PCSym pc form -> fromEnum pc

data PebbleModel = PebbleModel deriving Show

instance Model PebbleModel where
    type ParserType PebbleModel = PebbleParser (ScoredForest BestLogProb Rational)
    seqFromTune PebbleModel   = tuneChordDurs
    trainParser PebbleModel _ = mkPebbleParser . leftSplitProportionCounts

data HarmonyPebbleModel = HarmonyPebbleModel deriving Show

instance Model HarmonyPebbleModel where
    type ParserType HarmonyPebbleModel = 
        ProductParser (ScoredForest BestLogProb (StringSymbol, Ratio Integer)) 
                      (MapParser StringSymbol (ScoredForest BestLogProb StringSymbol)) 
                      (PebbleParser (ScoredForest BestLogProb Rational))
    seqFromTune HarmonyPebbleModel tune = 
        zip (seqFromTune HarmonyModel tune) 
            (seqFromTune PebbleModel  tune)
    trainParser HarmonyPebbleModel cs tunes = 
        ProductParser (trainParser HarmonyModel (map fst cs) tunes)
                      (trainParser PebbleModel  (map snd cs) tunes)   

data TransposedHarmonyPebbleModel = TransposedHarmonyPebbleModel deriving Show

instance Model TransposedHarmonyPebbleModel where
    type ParserType TransposedHarmonyPebbleModel = 
        ProductParser (ScoredForest BestLogProb (PitchClassSymbol, Rational)) 
                      (MapParser PitchClassSymbol (ScoredForest BestLogProb PitchClassSymbol)) 
                      (PebbleParser (ScoredForest BestLogProb Rational))
    seqFromTune TransposedHarmonyPebbleModel tune = 
        zip (seqFromTune TransposedHarmonyModel tune) 
            (seqFromTune PebbleModel            tune)
    trainParser TransposedHarmonyPebbleModel cs tunes = 
        ProductParser (trainParser TransposedHarmonyModel (map fst cs) tunes) 
                      (trainParser PebbleModel            (map snd cs) tunes)

data RhythmModel = RhythmModel deriving Show

instance Model RhythmModel where
    type ParserType RhythmModel = RhythmParser (ScoredForest BestLogProb ())
    seqFromTune RhythmModel = map (RCat 0) . tuneChordDurs
    -- trainParser RhythmModel _ _ = rhythmBestParser mkRhythmSampleParser
    trainParser RhythmModel _ tunes = rhythmBestParser 
                                    . flip evalRand gen
                                    . (>>= improveRhythmParser tunes)
                                    . (>>= improveRhythmParser tunes)
                                    . (improveRhythmParser tunes)
                                    $ mkRhythmSampleParser

data HarmonyRhythmModel = HarmonyRhythmModel deriving Show

instance Model HarmonyRhythmModel where
    type ParserType HarmonyRhythmModel =
        ProductParser (ScoredForest BestLogProb (StringSymbol, ())) 
                      (MapParser StringSymbol (ScoredForest BestLogProb StringSymbol)) 
                      (RhythmParser (ScoredForest BestLogProb ()))
    seqFromTune HarmonyRhythmModel tune = 
        zip (seqFromTune HarmonyModel tune) 
            (seqFromTune RhythmModel  tune)
    trainParser HarmonyRhythmModel cs tunes = 
        ProductParser (trainParser HarmonyModel (map fst cs) tunes)
                        (trainParser RhythmModel  (map snd cs) tunes)
                        
data TransposedHarmonyRhythmModel = TransposedHarmonyRhythmModel deriving Show

instance Model TransposedHarmonyRhythmModel where
    type ParserType TransposedHarmonyRhythmModel =
        ProductParser (ScoredForest BestLogProb (PitchClassSymbol, ())) 
                      (MapParser PitchClassSymbol (ScoredForest BestLogProb PitchClassSymbol))  
                      (RhythmParser (ScoredForest BestLogProb ()))
    seqFromTune TransposedHarmonyRhythmModel tune = 
        zip (seqFromTune TransposedHarmonyModel tune) 
            (seqFromTune RhythmModel  tune)
    trainParser TransposedHarmonyRhythmModel cs tunes = 
        ProductParser (trainParser TransposedHarmonyModel (map fst cs) tunes)
                      (trainParser RhythmModel  (map snd cs) tunes)

-----------------------
--- Random Baseline ---
-----------------------

randomBaselineAccs :: (RandomGen g) => [IRealTune] -> Rand g [Double]
randomBaselineAccs tunes = accs where
    seqs = take <$> (length . tuneChords <$> tunes) <*> pure (repeat S)
    goldTrees = forgetLeafLabels . tuneTree <$> tunes
    accs = do 
        randTrees <- sequence $ randomTree . parse allTreesParser <$> seqs
        return . zipWith constituentAccuracy goldTrees $ randTrees

calcRandBaselineAccs :: [IRealTune] -> [Double]
calcRandBaselineAccs = flip evalRand (mkStdGen 926406425) . randomBaselineAccs 

------------------------
--- Model Evaluation ---
------------------------

crossValidation :: [a] -> ([a] -> model) -> (model -> a -> b) -> [b]
crossValidation dataset train eval = do
    (testDatum, trainData) <- splits [] dataset
    let model = train trainData
    return . eval model $ testDatum

    where 
        splits :: [a] -> [a] -> [(a,[a])]
        splits _ [] = []
        splits left (a:right) = (a, left ++ right) : splits (left ++ [a]) right

evalModel :: ( p ~ ParserType m, Parser p, Model m
             , c ~ Category p, Ord c
             , s ~ Score p, s ~ ScoredForest BestLogProb b, Ord b
             ) 
          => m -> [IRealTune] -> [Double]
evalModel m tunes = crossValidation tunes (trainParser m chords) $ eval where
    chords = L.nub . join . map (seqFromTune m) $ tunes

    eval p tune = constituentAccuracy bestTree goldTree where
        bestTree = greedyBestTree . parse p . (seqFromTune m) $ tune
        goldTree = forgetLeafLabels . tuneTree $ tune

---------------------
--- Main Function ---
---------------------

foo = do
    tunes <- readIRealTunes
    let m = TransposedHarmonyPebbleModel
    let accs = evalModel m . take 75 $ tunes
    print m
    print accs
    print $ sum accs / (fromIntegral . length $ accs)
    return accs

---------------------
--- Working Space ----
---------------------

estimateValueCountsFromTunes :: ( RandomGen g, ParserSymScore p a s
                                , a ~ RhythmCategory
                                , s ~ ScoredForest (Log Double) b
                                , b ~ (Bool,RhythmRule)
                                )
                             => p -> [IRealTune] -> Rand g (M.Map b Double)
estimateValueCountsFromTunes p tunes = fmap (M.unionsWith (+)) 
                                     . sequence 
                                     . map (uncurry (estimateValueCounts p)) 
                                     . zip (map (spanConditionsFromTree . tuneTree) tunes) 
                                     $ map (seqFromTune RhythmModel) tunes

-- foo = do 
--     tunes <- take 100 <$> readIRealTunes
--     print . map (seqFromTune RhythmModel) $ tunes
--     let p = mkRhythmSampleParser
--     let rands = estimateValueCountsFromTunes p tunes
--     let cs = evalRand rands gen
--     return cs

-- foo = do
--     tunes <- take 75 <$> readIRealTunes
--     let p = rhythmBestParser 
--           . flip evalRand gen
--           . improveRhythmParser tunes
--           $ mkRhythmSampleParser
--     -- let f = logprob 
--     -- print . support . downbeatDist    downbeatDist p
--     let seqs = map (RCat 0) . tuneChordDurs <$> tunes
--     let bestTrees = greedyBestTree . parse p <$> seqs
--     let goldTrees = forgetLeafLabels . tuneTree <$> tunes
--     let accs = zipWith constituentAccuracy bestTrees goldTrees
--     print accs
--     print $ sum accs / (fromIntegral . length $ accs)
--     return accs

csvLine :: Show a => [a] -> String
csvLine []     = ""
csvLine [a]    = show a <> "\n"
csvLine (a:as) = show a <> "," <> csvLine as

writeIsmirData = do
    tunes <- take 75 <$> readIRealTunes
    let header = "model," <> csvLine [1..75]
    let baseline = "RandomBaseline," <> csvLine (calcRandBaselineAccs tunes)
    let csv = mconcat [ (show HarmonyModel <>) . ("," <>) . csvLine . evalModel HarmonyModel $ tunes
                      , (show TransposedHarmonyModel <>) . ("," <>) . csvLine . evalModel TransposedHarmonyModel $ tunes
                      , (show PebbleModel <>) . ("," <>) . csvLine . evalModel PebbleModel $ tunes
                      , (show HarmonyPebbleModel <>) . ("," <>) . csvLine . evalModel HarmonyPebbleModel $ tunes
                      , (show TransposedHarmonyPebbleModel <>) . ("," <>) . csvLine . evalModel TransposedHarmonyPebbleModel $ tunes
                      , (show RhythmModel <>) . ("," <>) . csvLine . evalModel RhythmModel $ tunes
                      , (show HarmonyRhythmModel <>) . ("," <>) . csvLine . evalModel HarmonyRhythmModel $ tunes
                      , (show TransposedHarmonyRhythmModel <>) . ("," <>) . csvLine . evalModel TransposedHarmonyRhythmModel $ tunes
                      ]
    putStr csv
    writeFile "ismirData.csv" (header <> baseline <> csv)

main = do
    writeHarmonyRuleCounts
    writeLeftSplitProportions
    writeIsmirData
