# incremental-nc-coins-problem

We formally prove (Lean), verify and construct (Lean, Julia, Haskell):

One incremental n x n Latin square can encode, given n,
**all** it's nc-coins problem solutions, for **all** thresholds c.

Our work improves upon 1990s 'Mao-Hua Le, Weixuan Li and T. Wang':

"A generalization of the n-queen problem" work in a few ways.

- we introduce a single cyclic Latin square approach

- the set of cases is much smaller

- execution is order n faster

- we provide a formal proof

## generating documentation

Scripts in directory `doc/sh`.

## references

https://aixiv.science/abs/aixiv.261114.000001

https://palomar-registry.org/entry?id=PALOMAR-2026-11-14-000018

## games

the following 1 person game lets you experiment solving (n,c)-coins placements

https://numisma-square-board-challenge-564364450410.europe-west1.run.app/

the following 2 person game lets you experiment forcing a draw in co-op mode and forcing a lose for opponent in adv mode.

https://linelimit-45.ai.studio/

