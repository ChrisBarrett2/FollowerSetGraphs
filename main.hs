{-
    Copyright   :  (c) Christopher Barrett 2016
    License     :  GPL
-}

import FollowerSetGraph 

validInput :: String -> Bool
validInput letters = all (\l -> l == '0'|| l == '1') letters 

prettyPrint :: ([[String]], [(Int, Int, String)]) -> IO () 
prettyPrint (vertices, edges) = do 
	putStrLn "Vertices (index, words): "
	printVertices vertices 1
	putStrLn "Edges (from, to, label): "
	printEdges edges
	putStr "\n"
	
printVertices :: [[String]] -> Int -> IO ()
printVertices [] iter = return ()
printVertices (vertex:vs) iter = do
	putStrLn $ (show iter) ++ " " ++ (show vertex)
	printVertices vs (iter+1)
	
printEdges :: [(Int, Int, String)] -> IO ()
printEdges [] = return ()
printEdges ((i,j,char):es) = do
	putStrLn $ show (i+1,j+1,char)
	printEdges es

main = do
	putStrLn "Enter forbidden words in sequence, or a blank line to generate the follower set graph:"
	loop []

loop :: [String] -> IO ()
loop forbiddenWords = do
	word <- getLine
	if not . validInput $ word then do
		putStrLn "Invalid input. Start over"
		loop []		
	else if null word then do
		putStrLn "The graph generated is:"
		prettyPrint $ constructGraph $ forbiddenWords
		main
	else loop (word:forbiddenWords)