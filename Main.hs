module Main where

{- Algorithm 3.1: GenPartitions(m) -}
-- m = sum of the values a_{N + 1}, a_{N + 2}, ...
recursivePartition :: Int -> Int -> Int -> [Int] -> [[Int]]
recursivePartition 0 _ _ partition = [partition]
recursivePartition m upperBound n partition = concatMap (\i -> recursivePartition (m - i) i (n + 1) $ partition ++ [i]) [1 .. min upperBound m]

generatePartitions :: Int -> [[Int]]
generatePartitions m = recursivePartition m m 0 []

{- Algorithm 3.3: GenPartitions2(m, n)
    We set the first (largest) part to have size n, and then generate all partitions of m - n
        in which all parts have size at most n.
-}
generatePartitions2 :: Int -> Int -> [[Int]]
generatePartitions2 m n = recursivePartition (m - n) n 1 [n]

{- Algorithm 3.4: GenPartitions3(m, n)
    Uses algorithm 3.2: ConjPartition(partition)
-}

-- I can't figure out what they want to do here, so I wrote my own version
-- conjugatePartition partition =
--   let b = replicate (head partition) 1
--    in concatMap (\j -> map ((b !!) . subtract 1) [1 .. (partition !!) $ subtract 1 j]) [2 .. length partition]

-- Count the amount of non-zero elements and then decrement them
conjugatePartitionRec :: [Int] -> [Int] -> [Int]
conjugatePartitionRec partition conjPartition
  | any (> 0) partition = conjugatePartitionRec (map (subtract 1) partition) $ conjPartition ++ [length $ filter (> 0) partition]
  | otherwise = conjPartition

conjugatePartition :: [Int] -> [Int]
conjugatePartition partition = conjugatePartitionRec partition []

recursivePartition2 :: Int -> Int -> Int -> [Int] -> [[Int]]
recursivePartition2 0 _ _ partition = [conjugatePartition partition]
recursivePartition2 m upperBound n partition = concatMap (\i -> recursivePartition2 (m - i) i (n + 1) $ partition ++ [i]) [1 .. min upperBound m]

-- Generate all the partitions of m into n parts
generatePartitions3 :: Int -> Int -> [[Int]]
generatePartitions3 m n = recursivePartition2 (m - n) n 1 [n]

{- Algorithm 3.5: Enumpartitions(m, n) -}
-- Find P(n, m) in a recursive manner
enumeratePartitions :: Int -> Int -> Int
enumeratePartitions 0 0 = 1
enumeratePartitions _ 0 = 0
enumeratePartitions m n = enumeratePartitions (m - 1) (n - 1) + addIfMGtN
  where
    addIfMGtN
      | m < 2 * n = 0
      | otherwise = enumeratePartitions (m - n) n

updateTable :: [[Int]] -> Int -> (Int, Int) -> [[Int]]
updateTable m x (r, c) =
  take r m
    ++ [take c (m !! r) ++ [x] ++ drop (c + 1) (m !! r)]
    ++ drop (r + 1) m

enumeratePartitionsLoop :: Int -> Int -> Int -> Int -> [[Int]] -> [[Int]]
enumeratePartitionsLoop i m j n table
  | i == (m + 1) = table
  | j == min i n + 1 = enumeratePartitionsLoop (i + 1) m 1 n table
  | otherwise = enumeratePartitionsLoop i m (j + 1) n $ flip (updateTable table) (i, j) $ table !! (i - 1) !! (j - 1) + addIfIGtJ
  where
    addIfIGtJ
      | i < 2 * j = 0
      | otherwise = table !! (i - j) !! j

-- Find P(n, m) in a dynamic manner, thus return the whole table leading up to this element
enumeratePartitions' :: Int -> Int -> [[Int]]
enumeratePartitions' m n = map tail $ drop 1 $ enumeratePartitionsLoop 1 m 1 n initTable
  where
    initTable = [map (el j) [0 .. n] | j <- [0 .. m]]
    el 0 0 = 1
    el _ _ = 0

{- Algorithm 3.8: PartitionLexRank(m, n, partition) -}
partitionLexRankHelp :: Int -> Int -> [Int] -> [[Int]] -> Int -> Int
partitionLexRankHelp 0 _ _ _ rank = rank
partitionLexRankHelp m n partition p rank
  | partition !! (n - 1) == 1 = partitionLexRankHelp (m - 1) (n - 1) partition p rank
  | otherwise = partitionLexRankHelp (m - n) n decrementedPartition p (rank + p !! (m - 2) !! (n - 2))
  where
    decrementedPartition = map (subtract 1) (take n partition) ++ drop n partition

partitionLexRank :: Int -> Int -> [Int] -> Int
partitionLexRank m n partition = partitionLexRankHelp m n partition (enumeratePartitions' m n) 0

{- Algorithm 3.7: PartitionLexSuccessor(m, n, partition) -}
takeWhile1Bigger :: [Int] -> [Int]
takeWhile1Bigger [] = []
takeWhile1Bigger (x : xs) = x : takeWhile (\y -> x <= y + 1) xs

-- The algorithm in the paper performs this weird loop thingy with the d variable that I don't really understand,
--  this is the formula implemented shown in the paper just before the algorithm
partitionLexSuccessor :: Int -> Int -> [Int] -> Maybe [Int]
partitionLexSuccessor m n partition
  | i == n + 1 = Nothing
  | otherwise = Just $ newHead : newMatched ++ drop (i + 1) partition
  where
    lastMatch = takeWhile1Bigger partition
    i = length lastMatch
    mismatchedElement = partition !! i + 1
    -- 2 -> 1 because we're 0-indexed
    newHead = sum lastMatch - (i - 1) * mismatchedElement - 1
    newMatched = replicate i mismatchedElement

{- Algorithm 3.9: PartitionLexUnrank(m, n, rank) -}
partitionLexUnrankHelp :: Int -> Int -> [Int] -> [[Int]] -> Int -> [Int]
partitionLexUnrankHelp 0 _ partition _ _ = partition
partitionLexUnrankHelp m n partition p rank
  | rank < topLeftP = partitionLexUnrankHelp (m - 1) (n - 1) (left ++ [head right + 1] ++ tail right) p rank
  | otherwise = partitionLexUnrankHelp (m - n) n incrementedPartition p (rank - topLeftP)
  where
    topLeftP
      | m == 1 = p !! (m - 1) !! (n - 1)
      | otherwise = p !! (m - 2) !! (n - 2)
    (left, right) = splitAt (n - 1) partition
    incrementedPartition = map (+ 1) (take n partition) ++ drop n partition

partitionLexUnrank :: Int -> Int -> Int -> [Int]
partitionLexUnrank m n = partitionLexUnrankHelp m n (replicate n 0) (enumeratePartitions' m n)

main :: IO ()
main = do
  -- print $ enumeratePartitions 4 2
  print $ partitionLexSuccessor 17 5 [5, 5, 4, 2, 1]