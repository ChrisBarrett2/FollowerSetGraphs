{-
    Copyright   :  (c) Christopher Barrett 2016
    License     :  GPL
-}

module FollowerSetGraph (
	constructGraph,
	testGraphs
) 	where

import Control.Monad
import Data.List
import Data.Function (on)
import Data.Ord (comparing)
import Data.Tuple
import qualified Data.Graph as G1 (buildG)
import qualified Data.Graph.Automorphism as G2 (isIsomorphic)

-- Returns all possible words up to length n
getWords :: Int -> [String]
getWords n = concat $ map (flip replicateM "01") [0..n]

-- returns only words of length N
getWordsN :: Int -> [String]
getWordsN n = replicateM n "01"

-- Needed because [a,b,c] /= [b,c,a]
listsSameElts :: Eq a => [a] -> [a] -> Bool 
listsSameElts xs ys = null (xs \\ ys) && null (ys \\ xs)

permuteZeroesAndOnes' :: String -> String
permuteZeroesAndOnes' [] = []
permuteZeroesAndOnes' (x:xs) = if x == '0' then '1' : permuteZeroesAndOnes' xs else '0' : permuteZeroesAndOnes' xs

permuteZeroesAndOnes :: [String] -> [String]
permuteZeroesAndOnes words = map permuteZeroesAndOnes' words

removePermutations :: [[String]] -> [[String]]
removePermutations [] = []
removePermutations (fs:fWords) = fs : removePermutations (filter (not . listsSameElts (permuteZeroesAndOnes fs)) fWords)

-- Use tail because we dont want the empty set - only sets of words of length n
-- Returns only words of length n
getSetsOfForbiddenWords n = removePermutations . tail . subsequences $ getWordsN n 

isAllowed :: [String] -> String -> Bool
isAllowed forbiddenWords word = not $ any (flip isInfixOf word) forbiddenWords

getAllowableWords :: [String] -> Int -> [String]
getAllowableWords forbiddenWords n = filter (isAllowed forbiddenWords) $ getWords n
 
followerVector :: [String] -> String -> [String]
followerVector words word = map (word ++) words

type FollowerTable = [(String, [String])]
type TruthTable = [(String, [Bool])]

followerTable :: [String] -> FollowerTable
followerTable words = map (\x -> (x, followerVector words x)) words

-- Takes (key, value) pairs and returns sets of keys which shared the same value
groupSets :: (Ord b) => [(a, b)] -> [[a]]
groupSets pairs = map (map fst) $ groupBy ((==) `on` snd) . sortBy (comparing snd) $ pairs

testForbidden :: [String] -> FollowerTable -> TruthTable
testForbidden forbiddenWords table = map (\(a,b) -> (a, map (isAllowed forbiddenWords) $ b)) table

addExtraLetterToFollowerSet :: Int -> [String] -> [String] -> Char -> [String]
addExtraLetterToFollowerSet k forbiddenWords mus letter = (filter (isAllowed forbiddenWords) longerMus)
	where longerMus = map ([letter] ++) . filter (\mu -> length mu == k)  $ mus

addExtraLettersToFollowerSets :: Int -> [String] -> [[String]] -> [[String]]
addExtraLettersToFollowerSets k fWords nodes = map (\node -> node ++ (addExtraLetterToFollowerSet k fWords node '0') ++ (addExtraLetterToFollowerSet k fWords node '1'))  nodes

-- Node is a list of words which are to be 'followed'. Ie the nodes on the graph.
-- Takes all allowable words of up to length k (with k+1 understood to be the length of the forbidden words) and creates a follower table out of them - that is, 
-- a list of pairs (allowed word, list of possible words following it - ie the word with added endings). The endings are added in the same manner every time.
-- This list then has its second element converted into True/False values, depending on whether that particular element is an allowed word or not.
-- Next, we "group" the sets, that is, return a list of lists of elements who's truth values are the same - ie, who have the same allowed follower words.
-- This gives us the 'nodes' of our FSG.
-- Finally, we add the allowed words of length k+1 to each 'node', by adding each letter "0" and "1" to each word of length k, and adding it if it is an allowed word.
getNodes :: Int -> [String] -> [[String]]
getNodes k forbiddenWords = addExtraLettersToFollowerSets k forbiddenWords . groupSets . testForbidden forbiddenWords . followerTable . getAllowableWords forbiddenWords $ k

-- Index of node source, index of node dest, label (0 or 1)
type MaybeEdge = (Maybe Int, Maybe Int, String)
type Edge = (Int, Int, String)

createEdge :: String -> [String] -> [[String]] -> MaybeEdge
createEdge add node nodes = (elemIndex node nodes, findIndex (elem addedLetter) nodes, add)
	where addedLetter = (head node) ++ add
	
eliminate :: [MaybeEdge] -> [Edge]
eliminate ((Just x, Just y, z):list) = (x, y, z):eliminate list
eliminate ((Just x, Nothing, z):list) = eliminate list
eliminate [] = []

getEdges :: [[String]] -> [Edge]
getEdges nodes = eliminate $ foldr (\node acc -> createEdge "0" node nodes : createEdge "1" node nodes : acc) [] nodes

-- Pairs of (node, edge) where node is a list of follower sets associated with that node
type Graph = ([[String]], [Edge])

constructGraph :: [String] -> Graph
constructGraph forbiddenWords =
	(nodes, edges)
	where
		k = (maximum $ map length forbiddenWords) - 1
		nodes = getNodes k forbiddenWords
		edges = getEdges nodes

-- Returns list of labels coming from each node. Nodes come in already sorted by first element
getLabelledEdgeSetSrc :: Graph -> [String]
getLabelledEdgeSetSrc g = sort . map (\edges -> concatMap tripleTrd edges) . groupBy ((==) `on` tripleFst) $ (snd g)

checkLabelledEdgeSetsSrc :: Graph -> Graph -> Bool
checkLabelledEdgeSetsSrc g1 g2 = getLabelledEdgeSetSrc g1 == getLabelledEdgeSetSrc g2

-- Returns list of labels going to each node
getLabelledEdgeSetDest :: Graph -> [String]
getLabelledEdgeSetDest g = sort . map (\edges -> concatMap tripleTrd edges) . groupBy ((==) `on` tripleSnd) . sortBy (comparing tripleSnd) $ (snd g)

checkLabelledEdgeSetsDest :: Graph -> Graph -> Bool
checkLabelledEdgeSetsDest g1 g2 = getLabelledEdgeSetDest g1 == getLabelledEdgeSetDest g2

-- returns (index, #emmitting)
getVertexSrc :: Graph -> [(Int, Int)]
getVertexSrc g = map (\edges -> (tripleFst . head $ edges, length edges)) . groupBy ((==) `on` tripleFst) . snd $ g

-- returns (index, #edges going to index)
getVertexDest :: Graph -> [(Int, Int)]
getVertexDest g = sortBy (comparing fst) . map (\edges -> (tripleSnd . head $ edges, length edges)) . groupBy ((==) `on` tripleSnd) . sortBy (comparing tripleSnd) . snd $ g

-- Takes (index, #emitting) and (index, #edges going to index) and returns the sorted list of number of edges at each node (ignoring direction)
sumEdges :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
sumEdges [] ys = ys
sumEdges xs [] = xs
sumEdges (x:xs) (y:ys) = if fst x == fst y then (fst x, snd x + snd y) : sumEdges xs ys else (if fst x > fst y then y : sumEdges (x:xs) ys else x : sumEdges xs (y:ys))

-- Returns sorted number of edges attached to each vertex
getUnlabelledEdgeSet :: Graph -> [Int]
getUnlabelledEdgeSet g = sort . map snd $ sumEdges (getVertexSrc g) (getVertexDest g)

checkUnlabelledEdgeSet g1 g2 = getUnlabelledEdgeSet g1 == getUnlabelledEdgeSet g2
 
getNumberCycles :: Graph -> Int
getNumberCycles g = length . filter (\(src, dest, lab) -> src == dest) $ snd g
	
checkCycles :: Graph -> Graph -> Bool
checkCycles g1 g2 = getNumberCycles g1 == getNumberCycles g2
	
checkNumberVertices g1 g2 = length (fst g1) == length (fst g2)

graphsCouldBeTheSame :: Graph -> Graph -> Bool
graphsCouldBeTheSame g1 g2 = (checkNumberVertices g1 g2) && (checkCycles g1 g2) && (checkUnlabelledEdgeSet g1 g2) && (checkLabelledEdgeSetsSrc g1 g2) && (checkLabelledEdgeSetsDest g1 g2) 
	
-- Returns (fWords, graph) pairs
createGraphsOfKValue :: Int -> [([String], Graph)]
createGraphsOfKValue k = map (\set -> (set, constructGraph set)) $ getSetsOfForbiddenWords (k+1)

-- Double check this is for digraphs and not just graphs?
myIsIsomorphic :: Graph -> Graph -> Bool
myIsIsomorphic g1 g2 = G2.isIsomorphic g1' g2'
	where 
		e1 = map (\(a,b,c) -> (a,b)) (snd g1)
		e2 = map (\(a,b,c) -> (a,b)) (snd g2)
		bounds1 = (0, length . fst $ g1)
		bounds2 = (0, length . fst $ g2)
		g1' = G1.buildG bounds1 e1
		g2' = G1.buildG bounds2 e2

-- takes x = (forbidden word set, graph) pair and compares against another list of graphs. Returns the sets of forbidden words that give isomorphic graphs to x
-- (including the forbidden words generating x itself)
testOneGraphAgainst :: ([String], Graph) -> [([String], Graph)] -> [[String]]
testOneGraphAgainst x [] = [fst x]
testOneGraphAgainst x (y:ys) = if graphsCouldBeTheSame (snd x) (snd y) && myIsIsomorphic (snd x) (snd y) then (fst y) : testOneGraphAgainst x ys else testOneGraphAgainst x ys

-- Takes a list of (fWords, graph) pairs and reutrns a list of sets of fWords that generate similar looking graphs
test :: [([String], Graph)] -> [[[String]]]
test [] = []
-- Dont test elements already noted to generate similar graphs to previous ones
test (x:xs) = similarForbiddenSets : (test $ filter (\(fs,g) -> not . flip elem similarForbiddenSets $ fs) xs)
	where similarForbiddenSets = testOneGraphAgainst x xs
	
testGraphs k = filter (\fs -> length fs > 1) . test $ (concatMap createGraphsOfKValue [1..k])

-- Helper functions
tripleFst :: (a,b,c) -> a
tripleFst (a,b,c) = a

tripleSnd :: (a,b,c) -> b
tripleSnd (a,b,c) = b

tripleTrd :: (a,b,c) -> c
tripleTrd (a,b,c) = c
