module Main where

import System.IO
import System.Environment (getArgs)
import Text.Read (readMaybe)
import Control.Concurrent (threadDelay)
import Control.Monad (forM_, when)
import Text.Printf (printf)

{-!
# Incremental Cyclic Latin Square & Generalized (n, c)-Coins in Haskell

This Haskell implementation translates the constructive incremental Latin square
from Lean 4 (`IncrementalCyclic.lean` & `n_c_coins_from_incremental.lean`).

## The Power of Laziness
In traditional backtracking n-coins solvers, laziness is famous for pruning
the search tree when asking for the first solution (`head (coins n)`).

With this **constructive formula**, we do not search at all: every cell is
determined in O(1) arithmetic operations:
    isCoin(i, j) <=> (i + q(j)) mod n < c

Haskell's laziness provides powerful advantages here:
1. **On-Demand Subgrid Evaluation**: To get the coin positions in row `i`,
   or to query the first `k` coins, laziness never computes or allocates
   the rest of the n × n board. For n = 1,000,000, `take 5 (coinsPositions n c)`
   runs in less than a millisecond!
2. **O(1) Streaming Memory**: Streaming an n × n board row-by-row runs in
   O(n) line-buffer memory (or O(1) beyond the current row) because consumed
   rows are immediately garbage-collected.
3. **Short-Circuiting Verification**: Verifying properties (e.g. `all (== c) rowCounts`)
   aborts at the very first violation without evaluating the remaining board.
-}

--------------------------------------------------------------------------------
-- 1. Permutation Families q(j)
--------------------------------------------------------------------------------

-- | Family 1: n ≡ 1, 5 (mod 6)
q1 :: Int -> Int -> Int
q1 n j
  | j == 0      = 0
  | 2 * j < n   = n - 2 * j
  | otherwise   = 2 * n - 2 * j

-- | Family 2: n ≡ 2, 4 (mod 6), n ≥ 10
q2 :: Int -> Int -> Int
q2 n j =
  let m = n `div` 2
  in if j < m
     then if 2 * j + m + 1 < n then 2 * j + m + 1 else 2 * j + m + 1 - n
     else if 2 * (j - m) + m + 4 < n then 2 * (j - m) + m + 4 else 2 * (j - m) + m + 4 - n

-- | Family 4: n ≡ 3 (mod 6), n ≥ 27
q4 :: Int -> Int -> Int
q4 n j =
  let k = n `div` 3
  in if j < k
     then if 3 * j + 2 * k < n then 3 * j + 2 * k else 3 * j + 2 * k - n
     else if j < 2 * k
          then if 3 * (j - k) + 2 * k + 4 < n then 3 * (j - k) + 2 * k + 4 else 3 * (j - k) + 2 * k + 4 - n
          else if 3 * (j - 2 * k) + 2 * k + 8 < n then 3 * (j - 2 * k) + 2 * k + 8 else 3 * (j - 2 * k) + 2 * k + 8 - n

-- | Family 3: n ≡ 0 (mod 6), n ≥ 12
q3 :: Int -> Int -> Int
q3 n j =
  let m = n `div` 2
  in if j == 0 then n - 2
     else if j < m - 2 then 2 * j + 2
     else if j == m - 2 then 0
     else if j < n - 1 then 2 * (j - (m - 1)) + 1
     else 2

-- | Small exceptional cases
q8, q9, q15, q21 :: Int -> Int
q8 j = [0, 4, 1, 3, 6, 2, 7, 5] !! (j `mod` 8)
q9 j = [0, 6, 3, 1, 8, 5, 2, 4, 7] !! (j `mod` 9)
q15 j = [0, 3, 6, 9, 12, 8, 5, 2, 13, 1, 4, 7, 10, 14, 11] !! (j `mod` 15)
q21 j = [0, 18, 15, 12, 9, 6, 3, 7, 4, 1, 14, 17, 10, 16, 2, 5, 11, 8, 20, 13, 19] !! (j `mod` 21)

-- | Master permutation dispatch
q :: Int -> Int -> Int
q n j
  | n == 8        = q8 j
  | n == 9        = q9 j
  | n == 15       = q15 j
  | n == 21       = q21 j
  | r == 1 || r == 5 = q1 n j
  | r == 2 || r == 4 = q2 n j
  | r == 3        = q4 n j
  | otherwise     = q3 n j
  where r = n `mod` 6

--------------------------------------------------------------------------------
-- 2. Cell Values and Lazy Board Generators
--------------------------------------------------------------------------------

-- | Value of cell (i, j) in the Incremental Latin Square
cellValue :: Int -> Int -> Int -> Int
cellValue n i j = (i + q n j) `mod` n

-- | True if cell (i, j) contains a coin in the (n, c)-coins placement
isCoin :: Int -> Int -> Int -> Int -> Bool
isCoin n c i j = cellValue n i j < c

-- | Lazy representation of the Incremental Board as a list of rows
incrementalBoard :: Int -> [[Int]]
incrementalBoard n = [ [ cellValue n i j | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- | Lazy representation of the (n, c)-Coins board as a list of rows of Bools
coinsBoard :: Int -> Int -> [[Bool]]
coinsBoard n c = [ [ isCoin n c i j | j <- [0 .. n - 1] ] | i <- [0 .. n - 1] ]

-- | Lazy stream of all coin coordinates (row, col) in order
coinsPositions :: Int -> Int -> [(Int, Int)]
coinsPositions n c =
  [ (i, j)
  | i <- [0 .. n - 1]
  , j <- [0 .. n - 1]
  , isCoin n c i j
  ]

-- | Coin column positions for a single row i (computed on demand!)
rowCoinCols :: Int -> Int -> Int -> [Int]
rowCoinCols n c i = [ j | j <- [0 .. n - 1], isCoin n c i j ]

--------------------------------------------------------------------------------
-- 3. Verification (Lazy short-circuiting)
--------------------------------------------------------------------------------

-- | Verify (n, c)-coins constraints with early-exit if any constraint fails
verifyCoins :: Int -> Int -> Bool
verifyCoins n c =
  rowsOk && colsOk && sumDiagsOk && diffDiagsOk
  where
    -- Each row has exactly c coins
    rowsOk = all (\i -> length (rowCoinCols n c i) == c) [0 .. n - 1]

    -- Each column has exactly c coins
    colsOk = all (\j -> length [ i | i <- [0 .. n - 1], isCoin n c i j ] == c) [0 .. n - 1]

    -- Each sum diagonal i + j = s has at most c coins
    sumDiagsOk = all (\s ->
      let cnt = length [ i | i <- [max 0 (s - n + 1) .. min (n - 1) s], isCoin n c i (s - i) ]
      in cnt <= c) [0 .. 2 * n - 2]

    -- Each diff diagonal i - j = d has at most c coins
    diffDiagsOk = all (\d ->
      let cnt = length [ i | i <- [max 0 d .. min (n - 1) (n - 1 + d)], isCoin n c i (i - d) ]
      in cnt <= c) [-(n - 1) .. n - 1]

--------------------------------------------------------------------------------
-- 4. Pretty Printing
--------------------------------------------------------------------------------

printIncremental :: Int -> IO ()
printIncremental n = do
  putStrLn $ "=== Incremental Board (" ++ show n ++ " × " ++ show n ++ ") ==="
  mapM_ (putStrLn . unwords . map show) (incrementalBoard n)

-- | Stream the Incremental Board cell-by-cell on the fly with an adjustable delay.
-- Each cell is computed and flushed to standard output immediately as it is generated,
-- demonstrating lazy, demand-driven evaluation without waiting for or allocating the whole board.
streamIncremental :: Int -> Int -> IO ()
streamIncremental n delayMs = do
  hSetBuffering stdout NoBuffering
  putStrLn $ "=== Streaming Incremental Board (" ++ show n ++ " × " ++ show n ++ ") on the fly ==="
  let width = length (show (n - 1))
  forM_ [0 .. n - 1] $ \i -> do
    forM_ [0 .. n - 1] $ \j -> do
      let val = cellValue n i j
      printf ("%" ++ show width ++ "d ") val
      hFlush stdout
      when (delayMs > 0) $ threadDelay (delayMs * 1000)
    putStrLn ""

-- | Stream the (n, c)-Coins Board cell-by-cell on the fly with adjustable delay.
streamCoins :: Int -> Int -> Int -> IO ()
streamCoins n c delayMs = do
  hSetBuffering stdout NoBuffering
  putStrLn $ "=== Streaming (" ++ show n ++ ", " ++ show c ++ ")-Coins Board on the fly ==="
  forM_ [0 .. n - 1] $ \i -> do
    forM_ [0 .. n - 1] $ \j -> do
      let coin = isCoin n c i j
      putStr (if coin then "C " else ". ")
      hFlush stdout
      when (delayMs > 0) $ threadDelay (delayMs * 1000)
    putStrLn ""

printCoins :: Int -> Int -> IO ()
printCoins n c = do
  putStrLn $ "=== (" ++ show n ++ ", " ++ show c ++ ")-Coins Solution ("
           ++ show n ++ " × " ++ show n ++ " board, " ++ show (n * c) ++ " coins) ==="
  mapM_ (putStrLn . unwords . map (\b -> if b then "C" else ".")) (coinsBoard n c)

--------------------------------------------------------------------------------
-- 5. Interactive UI & CLI
--------------------------------------------------------------------------------

prompt :: (Read a, Show a) => String -> a -> IO a
prompt msg defVal = do
  putStr msg
  hFlush stdout
  line <- getLine
  case readMaybe line of
    Just val -> return val
    Nothing  -> do
      putStrLn $ "Invalid input, using default: " ++ show defVal
      return defVal

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--incremental", nStr] -> case readMaybe nStr of
      Just n -> do
        printIncremental n
        -- putStrLn $ "Incremental verification: " ++ show (verifyCoins n 1)
      Nothing -> putStrLn "Invalid n"

    ["--stream", nStr] -> case readMaybe nStr of
      Just n -> streamIncremental n 25
      Nothing -> putStrLn "Invalid n"

    ["--stream", nStr, delayStr] -> case (readMaybe nStr, readMaybe delayStr) of
      (Just n, Just delayMs) -> streamIncremental n delayMs
      _ -> putStrLn "Invalid arguments for --stream"

    ["--stream-coins", nStr, cStr] -> case (readMaybe nStr, readMaybe cStr) of
      (Just n, Just c) -> streamCoins n c 25
      _ -> putStrLn "Invalid arguments for --stream-coins"

    ["--stream-coins", nStr, cStr, delayStr] -> case (readMaybe nStr, readMaybe cStr, readMaybe delayStr) of
      (Just n, Just c, Just delayMs) -> streamCoins n c delayMs
      _ -> putStrLn "Invalid arguments for --stream-coins"

    ["--coins", nStr, cStr] -> case (readMaybe nStr, readMaybe cStr) of
      (Just n, Just c) -> do
        printCoins n c
        -- putStrLn $ "Verification result: " ++ show (verifyCoins n c)
      _ -> putStrLn "Invalid arguments"

    ["--demo-laziness", nStr, cStr, kStr] -> case (readMaybe nStr, readMaybe cStr, readMaybe kStr) of
      (Just n, Just c, Just k) -> do
        putStrLn $ "=== Demonstrating Laziness for n = " ++ show n ++ ", c = " ++ show c ++ " ==="
        putStrLn $ "Extracting first " ++ show k ++ " coins without generating the remaining board..."
        let coins = take k (coinsPositions n c)
        mapM_ (\(idx, (r, col)) -> putStrLn $ "  Coin " ++ show idx ++ " at (" ++ show r ++ ", " ++ show col ++ ")") (zip [1..k] coins)
        putStrLn "Done instantaneously!"
      _ -> putStrLn "Invalid arguments for --demo-laziness"

    _ -> do
      putStrLn "=========================================================="
      putStrLn "  Haskell Incremental Board & (n, c)-Coins (Lazy Evaluation)"
      putStrLn "=========================================================="
      putStrLn "Choose an option:"
      putStrLn "  1. Generate Incremental Board (size n × n)"
      putStrLn "  2. Generate (n, c)-Coins Solution"
      putStrLn "  3. Demo Laziness: Instant query on massive n (e.g. n = 1,000,000)"
      putStrLn "  4. Stream on the fly (Educational demo with slowing down delay)"
      choice <- prompt "Enter choice (1, 2, 3, or 4): " (1 :: Int)
      case choice of
        2 -> do
          n <- prompt "Enter board size n: " (8 :: Int)
          c <- prompt ("Enter number of coins per row/col c (1 <= c <= " ++ show n ++ "): ") (3 :: Int)
          printCoins n c
          -- putStrLn "Verifying constraints..."
          -- putStrLn $ "Verification result: " ++ show (verifyCoins n c)

        3 -> do
          putStrLn "Imagine a board of size 100,000 × 100,000 (one trillion cells!)."
          n <- prompt "Enter massive n: " (1000000 :: Int)
          c <- prompt "Enter c: " (5 :: Int)
          k <- prompt "How many coin coordinates do you want to inspect? " (1000 :: Int)
          putStrLn $ "Streaming the first " ++ show k ++ " coin positions on demand..."
          let coins = take k (coinsPositions n c)
          mapM_ (\(idx, (r, col)) -> putStrLn $ "  Coin " ++ show idx ++ " -> row " ++ show r ++ ", col " ++ show col) (zip [1..k] coins)
          putStrLn "Notice how it computed instantaneously without allocating the trillion cells!"

        4 -> do
          putStrLn "--- Educational Streaming Demo ---"
          putStrLn "Watch values appear cell-by-cell in real time."
          putStrLn "Notice how each row is cyclically shifted by +1 (mod n) from the previous row!"
          mode <- prompt "What to stream? (1 = Incremental Board numbers, 2 = (n, c)-coins board): " (1 :: Int)
          n <- prompt "Enter board size n : " (8 :: Int)
          delayMs <- prompt "Enter slowing down delay per cell in ms : " (25 :: Int)
          if mode == 2
            then do
              c <- prompt ("Enter c (1 <= c <= " ++ show n ++ "): ") (3 :: Int)
              streamCoins n c delayMs
            else streamIncremental n delayMs

        _ -> do
          n <- prompt "Enter board size n: " (8 :: Int)
          printIncremental n
          -- putStrLn "Verifying 1-coins constraints..."
          -- putStrLn $ "Verification result: " ++ show (verifyCoins n 1)
