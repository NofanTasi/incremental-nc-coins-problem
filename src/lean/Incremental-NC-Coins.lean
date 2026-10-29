notation "ℕ" => Nat
/-!
# Executable Incremental Latin Square (Incremental Board) Generator

This program directly implements the constructive definitions from `IncrementalCyclic.lean`
and `n_c_coins_from_incremental.lean`.

## Time and Space Complexity
- Evaluating the permutation `p(j)` takes **$O(1)$ time** (a few arithmetic operations and `if-then-else`).
- Computing any cell `L(i, j) = (i + p(j)) % n` takes **$O(1)$ time**.
- Generating the complete $n \times n$ grid takes **$O(n^2)$ time and space**, which is asymptotically
  optimal (the grid has $n^2$ entries).
- Formatting and printing the board also runs in **$O(n^2)$ time**.
-/

namespace IncrementalCyclicProgram

/-- Family 1: `n ≡ 1, 5 (mod 6)` -/
def p1 (n j : ℕ) : ℕ :=
  if j = 0 then 0
  else if 2 * j < n then n - 2 * j
  else 2 * n - 2 * j

/-- Family 2: `n ≡ 2, 4 (mod 6)`, `n ≥ 10` -/
def p2 (n j : ℕ) : ℕ :=
  let m := n / 2
  if j < m then
    if 2 * j + m + 1 < n then 2 * j + m + 1 else 2 * j + m + 1 - n
  else
    if 2 * (j - m) + m + 4 < n then 2 * (j - m) + m + 4 else 2 * (j - m) + m + 4 - n

/-- Family 3: `n ≡ 3 (mod 6)`, `n ≥ 27` -/
def p3 (n j : ℕ) : ℕ :=
  let k := n / 3
  if j < k then
    if 3 * j + 2 * k < n then 3 * j + 2 * k else 3 * j + 2 * k - n
  else if j < 2 * k then
    if 3 * (j - k) + 2 * k + 4 < n then 3 * (j - k) + 2 * k + 4 else 3 * (j - k) + 2 * k + 4 - n
  else
    if 3 * (j - 2 * k) + 2 * k + 8 < n then 3 * (j - 2 * k) + 2 * k + 8 else 3 * (j - 2 * k) + 2 * k + 8 - n

/-- Family 4: `n ≡ 0 (mod 6)`, `n ≥ 12` -/
def p4 (n j : ℕ) : ℕ :=
  let m := n / 2
  if j = 0 then n - 2
  else if j < m - 2 then 2 * j + 2
  else if j = m - 2 then 0
  else if j < n - 1 then 2 * (j - (m - 1)) + 1
  else 2

/-- Exceptional small case: n = 8 -/
def p8 : ℕ → ℕ
  | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 7 | _ => 5

/-- Exceptional small case: n = 9 -/
def p9 : ℕ → ℕ
  | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 1 | 4 => 8 | 5 => 5 | 6 => 2 | 7 => 4 | _ => 7

/-- Exceptional small case: n = 15 -/
def p15 : ℕ → ℕ
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 9 | 4 => 12
  | 5 => 8 | 6 => 5 | 7 => 2 | 8 => 13 | 9 => 1
  | 10 => 4 | 11 => 7 | 12 => 10 | 13 => 14 | _ => 11

/-- Exceptional small case: n = 21 -/
def p21 : ℕ → ℕ
  | 0 => 0 | 1 => 18 | 2 => 15 | 3 => 12 | 4 => 9 | 5 => 6 | 6 => 3
  | 7 => 7 | 8 => 4 | 9 => 1 | 10 => 14 | 11 => 17 | 12 => 10 | 13 => 16
  | 14 => 2 | 15 => 5 | 16 => 11 | 17 => 8 | 18 => 20 | 19 => 13 | _ => 19

/-- Returns the column permutation `p : Fin n → Fin n` for all valid cyclic dimensions
    (`n ∉ {2, 3, 4, 6}`). Evaluates in O(1) time per column! -/
def getC (n : ℕ) (j : ℕ) : ℕ :=
  if n % 6 = 1 ∨ n % 6 = 5 then p1 n j
  else if n = 8 then p8 j
  else if (n % 6 = 2 ∨ n % 6 = 4) ∧ n ≥ 10 then p2 n j
  else if n = 9 then p9 j
  else if n = 15 then p15 j
  else if n = 21 then p21 j
  else if n % 6 = 3 ∧ n ≥ 27 then p3 n j
  else if n % 6 = 0 ∧ n ≥ 12 then p4 n j
  else 0

/-- Non-cyclic incremental Latin square for n = 4 -/
def L4 : ℕ → ℕ → ℕ
  | 0, 0 => 2 | 0, 1 => 0 | 0, 2 => 1 | 0, _ => 3
  | 1, 0 => 1 | 1, 1 => 3 | 1, 2 => 2 | 1, _ => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 3 | 2, _ => 1
  | _, 0 => 3 | _, 1 => 1 | _, 2 => 0 | _, _ => 2

/-- Non-cyclic incremental Latin square for n = 6 -/
def L6 : ℕ → ℕ → ℕ
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 2 | 0, 3 => 3 | 0, 4 => 5 | 0, _ => 4
  | 1, 0 => 3 | 1, 1 => 1 | 1, 2 => 4 | 1, 3 => 0 | 1, 4 => 2 | 1, _ => 5
  | 2, 0 => 4 | 2, 1 => 3 | 2, 2 => 5 | 2, 3 => 2 | 2, 4 => 1 | 2, _ => 0
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 5 | 3, 4 => 4 | 3, _ => 3
  | 4, 0 => 2 | 4, 1 => 5 | 4, 2 => 0 | 4, 3 => 4 | 4, 4 => 3 | 4, _ => 1
  | _, 0 => 5 | _, 1 => 4 | _, 2 => 3 | _, 3 => 1 | _, 4 => 0 | _, _ => 2

/-- Computes the cell value at row `i` and column `j` in O(1) time. -/
def cellValue (n : ℕ) (i j : ℕ) : ℕ :=
  if n = 4 then L4 i j
  else if n = 6 then L6 i j
  else (i + getC n j) % n

/-- Generates the complete n × n incremental Latin square board as an `Array (Array ℕ)` in O(n²) time. -/
def generateBoard (n : ℕ) : Array (Array ℕ) :=
  Array.ofFn (fun (i : Fin n) =>
    Array.ofFn (fun (j : Fin n) => cellValue n i.val j.val))

/-- Pretty-prints the n × n incremental board. -/
def printBoard (n : ℕ) : IO Unit := do
  if n = 2 ∨ n = 3 then
    IO.println s!"No incremental board exists for n = {n}."
  else
    -- IO.println s!"=== Incremental Board ({n} × {n}) ==="
    for i in [:n] do
      let mut rowStr := ""
      for j in [:n] do
        rowStr := rowStr ++ s!"{cellValue n i j} "
      IO.println rowStr

/-- Pretty-prints the (n, c)-coins solution obtained by thresholding the incremental board at `< c`.
    A cell is marked with 'C' (or '1') if occupied by a coin/coin, and '.' (or '0') otherwise. -/
def printCoinsBoard (n c : ℕ) : IO Unit := do
  if n = 2 ∨ n = 3 then
    IO.println s!"No generalized coins solution exists for n = {n}."
  else if c > n then
    IO.println s!"Invalid parameter c = {c}: must satisfy c ≤ n = {n}."
  else
    IO.println s!"({n}, {c})"
    for i in [:n] do
      let mut rowStr := ""
      for j in [:n] do
        let occupied := cellValue n i j < c
        rowStr := rowStr ++ (if occupied then "C " else ". ")
      IO.println rowStr

/-- Verifies in O(n²) time that a specific (n, c)-coins placement satisfies all row,
    column, and diagonal constraints. -/
def verifyCoinsPlacement (n c : ℕ) : Bool :=
  if c > n then false
  else
    -- 1. Check every row has at most c coins (in fact exactly c)
    let rowsOk := (List.range n).all fun i =>
      let count := (List.range n).foldl (fun cnt j => if cellValue n i j < c then cnt + 1 else cnt) 0
      count == c
    -- 2. Check every column has at most c coins (in fact exactly c)
    let colsOk := (List.range n).all fun j =>
      let count := (List.range n).foldl (fun cnt i => if cellValue n i j < c then cnt + 1 else cnt) 0
      count == c
    -- 3. Check downward diagonals (sum s) have at most c coins
    let sumOk := (List.range (2 * n - 1)).all fun s =>
      let count := (List.range n).foldl (fun cnt i =>
        if i ≤ s ∧ s - i < n then
          if cellValue n i (s - i) < c then cnt + 1 else cnt
        else cnt) 0
      count ≤ c
    -- 4. Check upward diagonals (diff d) have at most c coins
    let diffOk := (List.range (2 * n - 1)).all fun d_idx =>
      let d : Int := (d_idx : Int) - ((n : Int) - 1)
      let count := (List.range n).foldl (fun cnt (i : ℕ) =>
        let j_int : Int := (i : Int) - d
        if 0 ≤ j_int ∧ j_int < (n : Int) then
          if cellValue n i j_int.toNat < c then cnt + 1 else cnt
        else cnt) 0
      count ≤ c
    rowsOk && colsOk && sumOk && diffOk

/-- Diagnostic verifier: checks in O(n³) time that the generated board is indeed incremental. -/
def verifyIncremental (n : ℕ) : Bool :=
  -- 1. Check rows and cols are permutations
  let rowsOk := (List.range n).all fun i =>
    let row := (List.range n).map (fun j => cellValue n i j)
    row.eraseDups.length == n
  let colsOk := (List.range n).all fun j =>
    let col := (List.range n).map (fun i => cellValue n i j)
    col.eraseDups.length == n
  -- 2. Check diagonals for every threshold k < n
  let diagsOk := (List.range n).all fun k =>
    let sumOk := (List.range (2 * n - 1)).all fun s =>
      let count := (List.range n).foldl (fun cnt i =>
        if i ≤ s ∧ s - i < n then
          if cellValue n i (s - i) ≤ k then cnt + 1 else cnt
        else cnt) 0
      count ≤ k + 1
    let diffOk := (List.range (2 * n - 1)).all fun d_idx =>
      let d : Int := (d_idx : Int) - ((n : Int) - 1)
      let count := (List.range n).foldl (fun cnt (i : ℕ) =>
        let j_int : Int := (i : Int) - d
        if 0 ≤ j_int ∧ j_int < (n : Int) then
          if cellValue n i j_int.toNat ≤ k then cnt + 1 else cnt
        else cnt) 0
      count ≤ k + 1
    sumOk && diffOk
  rowsOk && colsOk && diagsOk

end IncrementalCyclicProgram

open IncrementalCyclicProgram

def main (args : List String) : IO Unit := do
  match args with
  | ["-incremental", nStr] =>
    let n := nStr.toNat?.getD 8
    printBoard n
  | ["-coins", nStr, cStr] =>
    let n := nStr.toNat?.getD 8
    let c := cStr.toNat?.getD 1
    printCoinsBoard n c
  | ["-incremental", "-v", nStr] =>
    let n := nStr.toNat?.getD 8
    printBoard n
    IO.println s!"Verifying incremental property for n = {n}..."
    let ok := verifyIncremental n
    IO.println s!"Result: {ok}"
  | ["-coins", "-v", nStr, cStr] =>
    let n := nStr.toNat?.getD 8
    let c := cStr.toNat?.getD 1
    printCoinsBoard n c
    IO.println s!"Verifying ({n}, {c})-coins constraints..."
    let ok := verifyCoinsPlacement n c
    IO.println s!"Result: {ok}"
  | _ =>
    IO.println ""


#eval printBoard 8
#eval IO.println ""
#eval printCoinsBoard 8 1
#eval IO.println ""
#eval printCoinsBoard 8 2
#eval IO.println ""
#eval printCoinsBoard 8 3
#eval IO.println ""
#eval printCoinsBoard 8 4
#eval IO.println ""
#eval printCoinsBoard 8 5
#eval IO.println ""
#eval printCoinsBoard 8 6
#eval IO.println ""
#eval printCoinsBoard 8 7
#eval IO.println ""
#eval printCoinsBoard 8 8
