#! /bin/bash

export ELAN_TOOLCHAIN="$(cat ../../src/lean/lean-toolchain)"

cd ../../src/lean

lean -c Incremental-NC-Coins.c Incremental-NC-Coins.lean
leanc -O3 Incremental-NC-Coins.c -o ../../bin/run/lean/Incremental-NC-Coins

rm Incremental-NC-Coins.c