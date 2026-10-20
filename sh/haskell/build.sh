#! /bin/bash

ghc -O2 ../../src/haskell/Incremental-NC-Coins.hs

mv ../../src/haskell/Incremental-NC-Coins ../../bin/run/haskell
rm ../../src/haskell/Incremental-NC-Coins.hi
rm ../../src/haskell/Incremental-NC-Coins.o

