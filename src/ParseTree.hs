{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module ParseTree
    ( FullTree(..)
    , headValue
    , leafValues
    , parseTree
    , parseLeafs
    , parseTreeBranches
    , treeBranches
    , phpSyntax
    , treeStringExample
    , ParseTree(..)
    , forgetLeafLabels
    , labelAndCombineLeafs
    , labelLeafs
    , labelConstituentSpans
    , constituentSpans
    , constituentAccuracy
    ) where

import Text.Parsec hiding (State)
import Control.Monad.Trans.State
import qualified Data.List as L

-- both inner nodes and leafs are labeled
data FullTree a = FT a [FullTree a]
    deriving (Show, Functor, Foldable)

headValue :: FullTree a -> a
headValue (FT a _) = a

leafValues :: FullTree a -> [a]
leafValues (FT a []) = [a]
leafValues (FT _ ts) = ts >>= leafValues

leaf :: Parsec String st (FullTree String)
leaf = FT <$> many (noneOf "[.] ") <*> pure []

node :: Parsec String st (FullTree String)
node = do
    string "[."
    lhs <- many (noneOf "[.] ")
    char ' '
    rhs <- tree `sepBy` char ' '
    char ']'
    return $ FT lhs (helper rhs)
    where helper [FT "" []] = []
          helper [] = []
          helper (t:ts) = t : helper ts
        
tree :: Parsec String st (FullTree String)
tree = node <|> leaf

parseTree :: String -> FullTree String
parseTree treeString = case parse tree "" treeString of 
    Right tree -> tree

parseLeafs :: String -> [String]
parseLeafs treeString = leafValues . parseTree $ treeString

parseTreeBranches :: String -> [[String]]
parseTreeBranches treeString = treeBranches . parseTree $ treeString

treeBranches :: FullTree a -> [[a]]
treeBranches (FT _ []) = []
treeBranches (FT a ts) = (a : map headValue ts) : (ts >>= treeBranches)

phpSyntax :: Show a => FullTree a -> String
phpSyntax (FT a ts) = "[" ++ show a ++ (concat . map phpSyntax $ ts) ++ "]"

treeStringExample :: String
treeStringExample = "[.Cm7 [.G7 [.Gsus Cm7 [.Gsus [.Fsus [.Ebsus Bbm7 [.Ebsus Dbsus Ebsus ] ] Fsus ] Gsus ] ] [.G7 Cm7 [.G7 [.Ab^7 [.Eb7 Bbm7 Eb7 ] Ab^7 ] [.G7 D%7 G7 ] ] ] ] Cm7 ]"

-- inner nodes are labeled, leafs are not labeled
data ParseTree a = PT a (ParseTree a) [ParseTree a] | Leaf
    deriving (Show, Functor, Foldable)

forgetLeafLabels :: FullTree a -> ParseTree a 
forgetLeafLabels (FT a []) = Leaf
forgetLeafLabels (FT a (t:ts)) = PT a (forgetLeafLabels t) (map forgetLeafLabels ts)

pop :: State [a] a
pop = do
    (a:as) <- get
    put as
    return a

labelAndCombineLeafs :: (Monoid b) => ParseTree a -> [b] -> FullTree b
labelAndCombineLeafs = evalState . state where
    state Leaf = FT <$> pop <*> pure []
    state (PT _ t ts) = do
        children <- traverse state (t:ts)
        return $ FT (foldMap headValue children) children

labelLeafs :: ParseTree a -> [a] -> FullTree a
labelLeafs = evalState . labelLeafs' where
    labelLeafs' :: ParseTree a -> State [a] (FullTree a)
    labelLeafs' Leaf = FT <$> pop <*> pure []
    labelLeafs' (PT a t ts) = FT a <$> traverse labelLeafs' (t:ts)

labelConstituentSpans :: ParseTree a -> FullTree (Int,Int)
labelConstituentSpans tree = evalState (labelSpans tree) $ spans where
    spans = zip [0..] [0..]
    labelSpans Leaf = FT <$> pop <*> pure []
    labelSpans (PT a t ts) = do 
        newChildren <- traverse labelSpans (t:ts)
        let childrenSpans = map headValue newChildren
        let newSpan = (fst . head $ childrenSpans, snd . last $ childrenSpans) 
        return (FT newSpan newChildren)

constituentSpans :: ParseTree a -> [(Int,Int)]
constituentSpans = foldr (:) [] . forgetLeafLabels . labelConstituentSpans

constituentAccuracy :: ParseTree a -> ParseTree b -> Double
constituentAccuracy t1 t2 = correctSpans / allSpans where
    sps1 = L.nub . constituentSpans $ t1
    sps2 = L.nub . constituentSpans $ t2
    correctSpans = fromIntegral . length $ sps1 `L.intersect` sps2
    allSpans     = fromIntegral . length $ sps1
