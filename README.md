# incremental-nc-coins-problem

We formally prove (Lean), verify and construct by code (Julia, Haskell):

One incremental n x n Latin square can encode, given n,
**all** it's nc-coins problem solutions, for all capacities c.

Our work improves upon
1990s 'Mao-Hua Le, Weixuan Li and T. Wang':
"A Generalization of the n-queen problem"
work in a few ways.

- we introduce a single Cyclic Latin square approach

- the set of cases is much smaller

- execution is order n faster

- we provide a formal proof.
