/-

Consider the following 8x8 "latin square" which is an "incremental board"

1 2 3 4 5 6 7 8
5 8 2 7 6 1 4 3
4 3 7 5 8 2 6 1
8 4 1 6 3 7 2 5
3 7 6 8 2 5 1 4
7 6 5 1 4 3 8 2
2 1 4 3 7 8 5 6
6 5 8 2 1 4 3 7


It is constructed as follows :

The construction of the incremental board builds the numbering layer by layer:

- Start with a valid n‑coins solution for the first layer (values equal to 1).

1 0 0 0 0 0 0 0
0 0 0 0 0 1 0 0
0 0 0 0 0 0 0 1
0 0 1 0 0 0 0 0
0 0 0 0 0 0 1 0
0 0 0 1 0 0 0 0
0 1 0 0 0 0 0 0
0 0 0 0 1 0 0 0

- For each next value c (from 2 to n), we choose a permutation
(one new coin per row and column) such that the cumulative set
of cells with values ≤ c satisfies the diagonal bound
(at most c occupied cells on any diagonal).

for c = 2

2 1 0 0 0 0 0 0
0 0 1 0 0 2 0 0
0 0 0 0 0 1 0 2
0 0 2 0 0 0 1 0
0 0 0 0 1 0 2 0
0 0 0 2 0 0 0 1
1 2 0 0 0 0 0 0
0 0 0 1 2 0 0 0

and so on

A key point: the new permutation alone (the cells with value exactly c)
need not be a valid n-coins solution. It can have diagonal conflicts,
as long as the total number of coins on any diagonal after adding it
does not exceed c.

Thus, the incremental board is not a simple sum of independent n-coins solutions.

Consider, again,

1 2 3 4 5 6 7 8
5 8 2 7 6 1 4 3
4 3 7 5 8 2 6 1
8 4 1 6 3 7 2 5
3 7 6 8 2 5 1 4
7 6 5 1 4 3 8 2
2 1 4 3 7 8 5 6
6 5 8 2 1 4 3 7

take 1 <= c <= n and change every k <= c by 1 and every k > c by 0

for n = 1 one obtains an (n, 1) coins solution

1 0 0 0 0 0 0 0
0 0 0 0 0 1 0 0
0 0 0 0 0 0 0 1
0 0 1 0 0 0 0 0
0 0 0 0 0 0 1 0
0 0 0 1 0 0 0 0
0 1 0 0 0 0 0 0
0 0 0 0 1 0 0 0

for n = 2 one obtains an (n, 2) coins solution

1 1 0 0 0 0 0 0
0 0 1 0 0 1 0 0
0 0 0 0 0 1 0 1
0 0 1 0 0 0 1 0
0 0 0 0 1 0 1 0
0 0 0 1 0 0 0 1
1 1 0 0 0 0 0 0
0 0 0 1 1 0 0 0

and so on

so far for the connection of incremental boards and (n, c) coins solutions :
incremental boards are n (n, c) coins solutions on one board.


for every n there exist a n nxn Latin Square Ln with Ln[i,j] = (i+j) mod n

let us call it the latin table Ln for the cyclic group Zn.

for example, L5

0 1 2 3 4
​1 2 3 4 0
2 3 4 0 1
3 4 0 1 2
4 0 1 2 3

adding the "all-ones" matrix to it yields

1 2 3 4 5
​2 3 4 5 1
3 4 5 1 2
4 5 1 2 3
5 1 2 3 4

it is not a incremental board, but, here is a conjecture (from my twin brother Marc)

for all n >= 7 there exists a permutation q such that  Un[i][j] = 1 + (i+q[j] mod n) is a incremental board.

There exist "families" of such permutations for specific numbers n,
for example, if gcd(n, 6) = 1, then q(j) = -2j mod n is a solution.

Maybe you can find a union of families covering all natural numbers?

Maybe you can provide another kind of proof?

-/

import Mathlib

namespace IncrementalCyclic

open Function (Bijective)
open Nat (mod_lt)
open Finset (univ)

open scoped Finset

def cyclicSquare
    (n : ℕ)
    (h : n > 0)
    (_ : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (q : Fin n → Fin n) :
  Fin n → Fin n → Fin n :=

    fun i j =>
      ⟨(i.val + (q j).val) % n, mod_lt _ h⟩

-- Cells on a diagonal of constant row + column,
-- whose symbols have value at most k.
def sumDiagOk
    (n : ℕ)
    (s : ℕ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun p : Fin n × Fin n =>
        p.1.val + p.2.val = s
      ∧ (L p.1 p.2).val ≤ k

-- Cells on a diagonal of constant row - column,
-- whose symbols have value at most k.
def diffDiagOk
    (n : ℕ)
    (d : ℤ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun p : Fin n × Fin n =>
        ((p.1.val : Int) - (p.2.val : Int)) = d
      ∧ (L p.1 p.2).val ≤ k

-- Every threshold set has at most k+1 cells on each
-- diagonal, for every threshold k < n.
def IsIncremental
    (n : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Prop :=

        (∀ i : Fin n, Bijective (L i .))
      ∧ (∀ j : Fin n, Bijective (L . j))
    ∧ ∀ k : ℕ,
        k < n →
          (∀ s : ℕ,   #(sumDiagOk  n s k L) ≤ k + 1)
        ∧ (∀ d : Int, #(diffDiagOk n d k L) ≤ k + 1)

def val_nat (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) : ℕ :=
  if i + q_nat j < n then i + q_nat j else i + q_nat j - n

lemma mod_eq_val_nat (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) (hi : i < n) (hq : q_nat j < n) :
    (i + q_nat j) % n = val_nat n q_nat i j := by
  dsimp only [val_nat]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have h1 : n ≤ i + q_nat j := by omega
    have h2 : i + q_nat j - n < n := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]

lemma val_nat_spec (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) :
    (i + q_nat j < n ∧ val_nat n q_nat i j = i + q_nat j) ∨
    (i + q_nat j ≥ n ∧ val_nat n q_nat i j = i + q_nat j - n) := by
  dsimp only [val_nat]; split_ifs <;> omega

lemma exists_incremental_of_nat
    (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (q_nat : ℕ → ℕ)
    (f_sum f_diff : ℕ → ℕ → ℕ)
    (hq_lt : ∀ j < n, q_nat j < n)
    (hq_inj : ∀ j₁ < n, ∀ j₂ < n, q_nat j₁ = q_nat j₂ → j₁ = j₂)
    (h_sum_le : ∀ i < n, ∀ j < n, f_sum i j ≤ val_nat n q_nat i j)
    (h_diff_le : ∀ i < n, ∀ j < n, f_diff i j ≤ val_nat n q_nat i j)
    (h_sum_inj : ∀ i₁ < n, ∀ j₁ < n, ∀ i₂ < n, ∀ j₂ < n,
      i₁ + j₁ = i₂ + j₂ → f_sum i₁ j₁ = f_sum i₂ j₂ → j₁ = j₂)
    (h_diff_inj : ∀ i₁ < n, ∀ j₁ < n, ∀ i₂ < n, ∀ j₂ < n,
      (i₁ : ℤ) - j₁ = (i₂ : ℤ) - j₂ → f_diff i₁ j₁ = f_diff i₂ j₂ → j₁ = j₂) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  let q : Fin n → Fin n := fun j => ⟨q_nat j.val, hq_lt j.val j.isLt⟩
  have hq_bij : Bijective q := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun j₁ j₂ heq => ?_, rfl⟩
    apply Fin.ext
    exact hq_inj j₁.val j₁.isLt j₂.val j₂.isLt (congrArg Fin.val heq)
  have hL_val : ∀ i j : Fin n, (cyclicSquare n h hn q i j).val = val_nat n q_nat i.val j.val := by
    intro i j
    exact mod_eq_val_nat n q_nat i.val j.val i.isLt (hq_lt j.val j.isLt)
  refine ⟨q, hq_bij, ?_, ?_, ?_⟩
  · intro i
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun j₁ j₂ heq => ?_, rfl⟩
    have hval : val_nat n q_nat i.val j₁.val = val_nat n q_nat i.val j₂.val := by
      have h1 := congrArg Fin.val heq
      dsimp only at h1
      rw [hL_val i j₁, hL_val i j₂] at h1
      exact h1
    have hq1 := hq_lt j₁.val j₁.isLt
    have hq2 := hq_lt j₂.val j₂.isLt
    have hv1 := val_nat_spec n q_nat i.val j₁.val
    have hv2 := val_nat_spec n q_nat i.val j₂.val
    have hq_eq : q_nat j₁.val = q_nat j₂.val := by omega
    exact Fin.ext (hq_inj j₁.val j₁.isLt j₂.val j₂.isLt hq_eq)
  · intro j
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i₁ i₂ heq => ?_, rfl⟩
    have hval : val_nat n q_nat i₁.val j.val = val_nat n q_nat i₂.val j.val := by
      have h1 := congrArg Fin.val heq
      dsimp only at h1
      rw [hL_val i₁ j, hL_val i₂ j] at h1
      exact h1
    have hi1 := i₁.isLt
    have hi2 := i₂.isLt
    have hq1 := hq_lt j.val j.isLt
    have hv1 := val_nat_spec n q_nat i₁.val j.val
    have hv2 := val_nat_spec n q_nat i₂.val j.val
    apply Fin.ext
    omega
  · intro k _hk
    refine ⟨fun s => ?_, fun d => ?_⟩
    · calc #(sumDiagOk n s k (cyclicSquare n h hn q))
        _ ≤ #(Finset.range (k + 1)) := by
          apply Finset.card_le_card_of_injOn (fun p : Fin n × Fin n => f_sum p.1.val p.2.val)
          · intro p hp
            rw [Finset.mem_coe, sumDiagOk, Finset.mem_filter] at hp
            rw [Finset.mem_coe, Finset.mem_range]
            dsimp only
            have hle := h_sum_le p.1.val p.1.isLt p.2.val p.2.isLt
            have hval := hL_val p.1 p.2
            omega
          · intro p₁ hp₁ p₂ hp₂ hfeq
            rw [Finset.mem_coe, sumDiagOk, Finset.mem_filter] at hp₁ hp₂
            have hj : p₁.2.val = p₂.2.val :=
              h_sum_inj p₁.1.val p₁.1.isLt p₁.2.val p₁.2.isLt
                p₂.1.val p₂.1.isLt p₂.2.val p₂.2.isLt
                (by omega) hfeq
            have hi : p₁.1.val = p₂.1.val := by omega
            exact Prod.ext (Fin.ext hi) (Fin.ext hj)
        _ = k + 1 := Finset.card_range (k + 1)
    · calc #(diffDiagOk n d k (cyclicSquare n h hn q))
        _ ≤ #(Finset.range (k + 1)) := by
          apply Finset.card_le_card_of_injOn (fun p : Fin n × Fin n => f_diff p.1.val p.2.val)
          · intro p hp
            rw [Finset.mem_coe, diffDiagOk, Finset.mem_filter] at hp
            rw [Finset.mem_coe, Finset.mem_range]
            dsimp only
            have hle := h_diff_le p.1.val p.1.isLt p.2.val p.2.isLt
            have hval := hL_val p.1 p.2
            omega
          · intro p₁ hp₁ p₂ hp₂ hfeq
            rw [Finset.mem_coe, diffDiagOk, Finset.mem_filter] at hp₁ hp₂
            have hj : p₁.2.val = p₂.2.val :=
              h_diff_inj p₁.1.val p₁.1.isLt p₁.2.val p₁.2.isLt
                p₂.1.val p₂.1.isLt p₂.2.val p₂.2.isLt
                (by omega) hfeq
            have hi : p₁.1.val = p₂.1.val := by omega
            exact Prod.ext (Fin.ext hi) (Fin.ext hj)
        _ = k + 1 := Finset.card_range (k + 1)

/-! ### Family 1: `n ≡ 1, 5 (mod 6)` -/

def q1_nat (n j : ℕ) : ℕ :=
  if j = 0 then 0
  else if 2 * j < n then n - 2 * j
  else 2 * n - 2 * j

lemma q1_nat_spec (n j : ℕ) :
    (j = 0 ∧ q1_nat n j = 0) ∨
    (j > 0 ∧ 2 * j < n ∧ q1_nat n j = n - 2 * j) ∨
    (j > 0 ∧ 2 * j ≥ n ∧ q1_nat n j = 2 * n - 2 * j) := by
  dsimp only [q1_nat]; split_ifs <;> omega

lemma solve_family1 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  apply exists_incremental_of_nat n h hn (q1_nat n)
    (val_nat n (q1_nat n)) (val_nat n (q1_nat n))
  · intro j hj; have := q1_nat_spec n j; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    have := q1_nat_spec n j₁; have := q1_nat_spec n j₂; omega
  · intro i _ j _; exact le_rfl
  · intro i _ j _; exact le_rfl
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    have := q1_nat_spec n j₁; have := q1_nat_spec n j₂
    have := val_nat_spec n (q1_nat n) i₁ j₁; have := val_nat_spec n (q1_nat n) i₂ j₂
    omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    have := q1_nat_spec n j₁; have := q1_nat_spec n j₂
    have := val_nat_spec n (q1_nat n) i₁ j₁; have := val_nat_spec n (q1_nat n) i₂ j₂
    omega

/-! ### Family 2: `n ≡ 2, 4 (mod 6)`, `n ≥ 10` -/

def q2_nat (n j : ℕ) : ℕ :=
  let m := n / 2
  if j < m then
    if 2 * j + m + 1 < n then 2 * j + m + 1 else 2 * j + m + 1 - n
  else
    if 2 * (j - m) + m + 4 < n then 2 * (j - m) + m + 4 else 2 * (j - m) + m + 4 - n

lemma q2_nat_lt (n j : ℕ) (hj : j < n / 2) :
    (2 * j + n / 2 + 1 < n ∧ q2_nat n j = 2 * j + n / 2 + 1) ∨
    (2 * j + n / 2 + 1 ≥ n ∧ q2_nat n j = 2 * j + n / 2 + 1 - n) := by
  dsimp only [q2_nat]; split_ifs <;> omega

lemma q2_nat_ge (n j : ℕ) (hj : ¬ j < n / 2) :
    (2 * (j - n / 2) + n / 2 + 4 < n ∧ q2_nat n j = 2 * (j - n / 2) + n / 2 + 4) ∨
    (2 * (j - n / 2) + n / 2 + 4 ≥ n ∧ q2_nat n j = 2 * (j - n / 2) + n / 2 + 4 - n) := by
  dsimp only [q2_nat]; split_ifs <;> omega

def f2_sum (n i j : ℕ) : ℕ :=
  if i < 3 ∧ j ≥ n - 3 then j - (n - 3) else val_nat n (q2_nat n) i j

def f2_diff (n i j : ℕ) : ℕ :=
  if i = n - 1 ∧ j = n - 1 then 1 else val_nat n (q2_nat n) i j

lemma f2_sum_lt_spec (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_sum n i j ≤ val_nat n (q2_nat n) i j ∧ f2_sum n i j < n ∧
    (f2_sum n i j = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hq := q2_nat_lt n j hj
  have hv := val_nat_spec n (q2_nat n) i j
  have hf : f2_sum n i j = val_nat n (q2_nat n) i j := by
    dsimp only [f2_sum]; split_ifs <;> omega
  omega

lemma f2_sum_ge_spec (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_sum n i j ≤ val_nat n (q2_nat n) i j ∧ f2_sum n i j < n ∧
    ((i < 3 ∧ j ≥ n - 3 ∧ f2_sum n i j = j - (n - 3)) ∨
     ((i ≥ 3 ∨ j < n - 3) ∧
      (f2_sum n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hq := q2_nat_ge n j hjge
  have hv := val_nat_spec n (q2_nat n) i j
  dsimp only [f2_sum]; split_ifs <;> omega

lemma f2_diff_lt_spec (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_diff n i j ≤ val_nat n (q2_nat n) i j ∧ f2_diff n i j < n ∧
    (f2_diff n i j = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hq := q2_nat_lt n j hj
  have hv := val_nat_spec n (q2_nat n) i j
  have hf : f2_diff n i j = val_nat n (q2_nat n) i j := by
    dsimp only [f2_diff]; split_ifs <;> omega
  omega

lemma f2_diff_ge_spec (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_diff n i j ≤ val_nat n (q2_nat n) i j ∧ f2_diff n i j < n ∧
    ((i = n - 1 ∧ j = n - 1 ∧ f2_diff n i j = 1) ∨
     (i + j < 2 * n - 2 ∧
      (f2_diff n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hq := q2_nat_ge n j hjge
  have hv := val_nat_spec n (q2_nat n) i j
  dsimp only [f2_diff]; split_ifs <;> omega

lemma solve_family2 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 2 ∨ n % 6 = 4) (hge : n ≥ 10) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  have heven : n % 2 = 0 := by omega
  apply exists_incremental_of_nat n h hn (q2_nat n) (f2_sum n) (f2_diff n)
  · intro j hj
    by_cases h1 : j < n / 2
    · have := q2_nat_lt n j h1; omega
    · have := q2_nat_ge n j h1; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := q2_nat_lt n j₁ h1; have := q2_nat_lt n j₂ h2; omega
    · have := q2_nat_lt n j₁ h1; have := q2_nat_ge n j₂ h2; omega
    · have := q2_nat_ge n j₁ h1; have := q2_nat_lt n j₂ h2; omega
    · have := q2_nat_ge n j₁ h1; have := q2_nat_ge n j₂ h2; omega
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_sum_lt_spec n i j hge heven hi h1).1
    · exact (f2_sum_ge_spec n i j hge heven hi hj h1).1
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_diff_lt_spec n i j hge heven hi h1).1
    · exact (f2_diff_ge_spec n i j hge heven hi hj h1).1
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_sum_lt_spec n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_lt_spec n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_lt_spec n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_ge_spec n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_sum_ge_spec n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_lt_spec n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_ge_spec n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_ge_spec n i₂ j₂ hge heven hi₂ hj₂ h2; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_diff_lt_spec n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_lt_spec n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_lt_spec n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_ge_spec n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_diff_ge_spec n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_lt_spec n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_ge_spec n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_ge_spec n i₂ j₂ hge heven hi₂ hj₂ h2; omega

/-! ### Family 4: `n ≡ 3 (mod 6)`, `n ≥ 27` -/

def q4_nat (n j : ℕ) : ℕ :=
  let k := n / 3
  if j < k then
    if 3 * j + 2 * k < n then 3 * j + 2 * k else 3 * j + 2 * k - n
  else if j < 2 * k then
    if 3 * (j - k) + 2 * k + 4 < n then 3 * (j - k) + 2 * k + 4 else 3 * (j - k) + 2 * k + 4 - n
  else
    if 3 * (j - 2 * k) + 2 * k + 8 < n then 3 * (j - 2 * k) + 2 * k + 8 else 3 * (j - 2 * k) + 2 * k + 8 - n

lemma q4_nat_0 (n j : ℕ) (hj : j < n / 3) :
    (3 * j + 2 * (n / 3) < n ∧ q4_nat n j = 3 * j + 2 * (n / 3)) ∨
    (3 * j + 2 * (n / 3) ≥ n ∧ q4_nat n j = 3 * j + 2 * (n / 3) - n) := by
  dsimp only [q4_nat]; split_ifs <;> omega

lemma q4_nat_1 (n j : ℕ) (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    (3 * (j - n / 3) + 2 * (n / 3) + 4 < n ∧ q4_nat n j = 3 * (j - n / 3) + 2 * (n / 3) + 4) ∨
    (3 * (j - n / 3) + 2 * (n / 3) + 4 ≥ n ∧ q4_nat n j = 3 * (j - n / 3) + 2 * (n / 3) + 4 - n) := by
  dsimp only [q4_nat]; split_ifs <;> omega

lemma q4_nat_2 (n j : ℕ) (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    (3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 < n ∧ q4_nat n j = 3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8) ∨
    (3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 ≥ n ∧ q4_nat n j = 3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 - n) := by
  dsimp only [q4_nat]; split_ifs <;> omega

def f4_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (q4_nat n) i j
  let k := n / 3
  if i < 4 ∧ (j = n - 4 ∨ j = n - 3) then v - k
  else if i < 4 ∧ (j = n - 2 ∨ j = n - 1) then v - 2 * k
  else v

def f4_diff (n i j : ℕ) : ℕ :=
  let v := val_nat n (q4_nat n) i j
  let k := n / 3
  if i ≥ n - 2 ∧ j = n - 2 then v - 2 * k
  else if i ≥ n - 2 ∧ j = n - 1 then v - k
  else v

lemma f4_sum_0_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f4_sum n i j < n ∧
    (f4_sum n i j = i + 3 * j + 2 * (n / 3) ∨
     f4_sum n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hq := q4_nat_0 n j hj
  have hv := val_nat_spec n (q4_nat n) i j
  have hf : f4_sum n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_sum]; split_ifs <;> omega
  omega

lemma f4_sum_1_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f4_sum n i j < n ∧
    (f4_sum n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hq := q4_nat_1 n j hj1 hj2
  have hv := val_nat_spec n (q4_nat n) i j
  have hf : f4_sum n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_sum]; split_ifs <;> omega
  omega

lemma f4_sum_2_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f4_sum n i j < n ∧
    ((i < 4 ∧ (j = n - 4 ∨ j = n - 3) ∧ f4_sum n i j + 3 * n = i + 3 * j + n / 3 + 8) ∨
     (i < 4 ∧ (j = n - 2 ∨ j = n - 1) ∧ f4_sum n i j + 3 * n = i + 3 * j + 8) ∨
     ((i ≥ 4 ∨ j < n - 4) ∧
      (f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_sum n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hq := q4_nat_2 n j hj1 hj2
  have hv := val_nat_spec n (q4_nat n) i j
  dsimp only [f4_sum]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma f4_diff_0_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f4_diff n i j < n ∧
    (f4_diff n i j = i + 3 * j + 2 * (n / 3) ∨
     f4_diff n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hq := q4_nat_0 n j hj
  have hv := val_nat_spec n (q4_nat n) i j
  have hf : f4_diff n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_diff]; split_ifs <;> omega
  omega

lemma f4_diff_1_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f4_diff n i j < n ∧
    (f4_diff n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hq := q4_nat_1 n j hj1 hj2
  have hv := val_nat_spec n (q4_nat n) i j
  have hf : f4_diff n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_diff]; split_ifs <;> omega
  omega

lemma f4_diff_2_spec (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f4_diff n i j < n ∧
    ((i ≥ n - 2 ∧ j = n - 2 ∧ f4_diff n i j + n = i + 2) ∨
     (i ≥ n - 2 ∧ j = n - 1 ∧ f4_diff n i j + 2 * (n / 3) = i + 5) ∨
     ((i < n - 2 ∨ j < n - 2) ∧
      (f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_diff n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hq := q4_nat_2 n j hj1 hj2
  have hv := val_nat_spec n (q4_nat n) i j
  dsimp only [f4_diff]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma solve_family4 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 3) (hge : n ≥ 27) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  apply exists_incremental_of_nat n h hn (q4_nat n) (f4_sum n) (f4_diff n)
  · intro j hj
    by_cases h1 : j < n / 3
    · have := q4_nat_0 n j h1; omega
    · by_cases h2 : j < 2 * (n / 3)
      · have := q4_nat_1 n j h1 h2; omega
      · have := q4_nat_2 n j h1 h2; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := q4_nat_0 n j₁ h1a; have := q4_nat_0 n j₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := q4_nat_0 n j₁ h1a; have := q4_nat_1 n j₂ h2a h2b; omega
      · have := q4_nat_0 n j₁ h1a; have := q4_nat_2 n j₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := q4_nat_1 n j₁ h1a h1b; have := q4_nat_0 n j₂ h2a; omega
      · have := q4_nat_2 n j₁ h1a h1b; have := q4_nat_0 n j₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := q4_nat_1 n j₁ h1a h1b; have := q4_nat_1 n j₂ h2a h2b; omega
      · have := q4_nat_1 n j₁ h1a h1b; have := q4_nat_2 n j₂ h2a h2b; omega
      · have := q4_nat_2 n j₁ h1a h1b; have := q4_nat_1 n j₂ h2a h2b; omega
      · have := q4_nat_2 n j₁ h1a h1b; have := q4_nat_2 n j₂ h2a h2b; omega
  · intro i _ j _; dsimp only [f4_sum]; split_ifs <;> omega
  · intro i _ j _; dsimp only [f4_diff]; split_ifs <;> omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f4_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
      have := f4_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f4_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f4_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f4_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
      have := f4_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f4_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f4_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega

/-! ### Family 3: `n ≡ 0 (mod 6)`, `n ≥ 12` -/

def q3_nat (n j : ℕ) : ℕ :=
  let m := n / 2
  if j = 0 then n - 2
  else if j < m - 2 then 2 * j + 2
  else if j = m - 2 then 0
  else if j < n - 1 then 2 * (j - (m - 1)) + 1
  else 2

lemma q3_nat_lt (n j : ℕ) (hj : j < n / 2 - 1) :
    (j = 0 ∧ q3_nat n j = n - 2) ∨
    (1 ≤ j ∧ j < n / 2 - 2 ∧ q3_nat n j = 2 * j + 2) ∨
    (j = n / 2 - 2 ∧ q3_nat n j = 0) := by
  dsimp only [q3_nat]
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨by omega, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h3, rfl⟩)
  · omega
  · omega

lemma q3_nat_ge (n j : ℕ) (hge : n ≥ 12) (hj : ¬ j < n / 2 - 1) (hjlt : j < n) :
    (n / 2 - 1 ≤ j ∧ j < n - 1 ∧ q3_nat n j = 2 * (j - (n / 2 - 1)) + 1) ∨
    (j = n - 1 ∧ q3_nat n j = 2) := by
  dsimp only [q3_nat]
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · omega
  · exact Or.inl ⟨by omega, h4, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

def f3_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (q3_nat n) i j
  let m := n / 2
  if j = m - 1 ∧ i < n - 1 then v - 1
  else if j = n - 5 ∧ i + j < n then v - (m - 2)
  else if j = n - 1 ∧ i < 2 then v - 1
  else v

def f3_diff (n i j : ℕ) : ℕ :=
  let v := val_nat n (q3_nat n) i j
  let m := n / 2
  let k := n / 3
  if 1 + k ≤ j ∧ j ≤ m - 3 ∧ i ≥ k then v - 1
  else if j = m - 1 + k ∧ i ≥ k ∧ i < 2 * k then v - 1
  else if j = m - 1 + k ∧ i ≥ 2 * k ∧ n = 12 then v - 4
  else if j = m - 1 + k ∧ i ≥ 2 * k ∧ n ≠ 12 then v - 5
  else if m + k ≤ j ∧ j ≤ n - 2 ∧ i ≥ k then v - 2
  else v

lemma f3_sum_0_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f3_sum n i j < n ∧
    ((j = 0 ∧ (f3_sum n i j = i + n - 2 ∨ f3_sum n i j + 2 = i)) ∨
     (1 ≤ j ∧ j < n / 2 - 2 ∧ (f3_sum n i j = i + 2 * j + 2 ∨ f3_sum n i j + n = i + 2 * j + 2)) ∨
     (j = n / 2 - 2 ∧ f3_sum n i j = i)) := by
  have hq := q3_nat_lt n j hj
  have hv := val_nat_spec n (q3_nat n) i j
  have hf : f3_sum n i j = val_nat n (q3_nat n) i j := by
    dsimp only [f3_sum]; split_ifs <;> omega
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine ⟨by omega, Or.inl ⟨h1, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h1, h2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨h1, by omega⟩)⟩

lemma f3_sum_1_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n - 5) :
    f3_sum n i j < n ∧
    ((j = n / 2 - 1 ∧ i < n - 1 ∧ f3_sum n i j = i) ∨
     (j = n / 2 - 1 ∧ i = n - 1 ∧ f3_sum n i j = 0) ∨
     (n / 2 ≤ j ∧ j < n - 5 ∧
      (f3_sum n i j + n = i + 2 * j + 3 ∨ f3_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hq := q3_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_spec n (q3_nat n) i j
  dsimp only [f3_sum]
  split_ifs with hs1 hs2 hs3
  · refine ⟨by omega, Or.inl ⟨hs1.1, hs1.2, by omega⟩⟩
  · omega
  · omega
  · by_cases hjm : j = n / 2 - 1
    · refine ⟨by omega, Or.inr (Or.inl ⟨hjm, by omega, by omega⟩)⟩
    · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, hj2, by omega⟩)⟩

lemma f3_sum_2_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
    (hj2 : ¬ j < n - 5) :
    f3_sum n i j < n ∧
    ((j = n - 5 ∧ i < 5 ∧ f3_sum n i j = i + n / 2 - 5) ∨
     (j = n - 1 ∧ i < 2 ∧ f3_sum n i j = i + 1) ∨
     (j = n - 1 ∧ i ≥ 2 ∧ (f3_sum n i j = i + 2 ∨ f3_sum n i j + n = i + 2)) ∨
     (j < n - 1 ∧ (j ≠ n - 5 ∨ i ≥ 5) ∧
      (f3_sum n i j + n = i + 2 * j + 3 ∨ f3_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hq := q3_nat_ge n j hge (by omega) hjlt
  have hv := val_nat_spec n (q3_nat n) i j
  by_cases hjn1 : j = n - 1
  · have hq1 : q3_nat n j = 2 := by rcases hq with ⟨_, hlt, _⟩ | ⟨_, hq1⟩ <;> omega
    by_cases hi2 : i < 2
    · have hf : f3_sum n i j = val_nat n (q3_nat n) i j - 1 := by
        dsimp only [f3_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inl ⟨hjn1, hi2, by omega⟩)⟩
    · have hf : f3_sum n i j = val_nat n (q3_nat n) i j := by
        dsimp only [f3_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hjn1, by omega, by omega⟩))⟩
  · have hq1 : q3_nat n j = 2 * (j - (n / 2 - 1)) + 1 := by
      rcases hq with ⟨_, _, hq1⟩ | ⟨hjn, _⟩ <;> omega
    by_cases hj5 : j = n - 5 ∧ i < 5
    · have hf : f3_sum n i j = val_nat n (q3_nat n) i j - (n / 2 - 2) := by
        dsimp only [f3_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inl ⟨hj5.1, hj5.2, by omega⟩⟩
    · have hf : f3_sum n i j = val_nat n (q3_nat n) i j := by
        dsimp only [f3_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩

lemma f3_diff_0_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f3_diff n i j < n ∧
    ((j = 0 ∧ (f3_diff n i j = i + n - 2 ∨ f3_diff n i j + 2 = i)) ∨
     (j = n / 2 - 2 ∧ f3_diff n i j = i) ∨
     (1 + n / 3 ≤ j ∧ j ≤ n / 2 - 3 ∧ i ≥ n / 3 ∧ f3_diff n i j + n = i + 2 * j + 1) ∨
     (1 ≤ j ∧ j ≤ n / 2 - 3 ∧ (j < 1 + n / 3 ∨ i < n / 3) ∧
      (f3_diff n i j = i + 2 * j + 2 ∨ f3_diff n i j + n = i + 2 * j + 2))) := by
  have hq := q3_nat_lt n j hj
  have hv := val_nat_spec n (q3_nat n) i j
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
      dsimp only [f3_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inl ⟨h1, by omega⟩⟩
  · by_cases hw : 1 + n / 3 ≤ j ∧ i ≥ n / 3
    · have hf : f3_diff n i j = val_nat n (q3_nat n) i j - 1 := by
        dsimp only [f3_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hw.1, by omega, hw.2, by omega⟩))⟩
    · have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
        dsimp only [f3_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr ⟨h1, by omega, by omega, by omega⟩))⟩
  · have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
      dsimp only [f3_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inr (Or.inl ⟨h1, by omega⟩)⟩

lemma f3_diff_1_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n / 2 - 1 + n / 3) :
    f3_diff n i j < n ∧
    (f3_diff n i j + n = i + 2 * j + 3 ∨ f3_diff n i j + 2 * n = i + 2 * j + 3) := by
  have hq := q3_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_spec n (q3_nat n) i j
  have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
    dsimp only [f3_diff]; split_ifs <;> omega
  rcases hq with ⟨_, _, hq1⟩ | ⟨hjn, _⟩ <;> omega

lemma f3_diff_2_spec (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
    (hj2 : ¬ j < n / 2 - 1 + n / 3) :
    f3_diff n i j < n ∧
    ((j = n / 2 - 1 + n / 3 ∧ n / 3 ≤ i ∧ i < 2 * (n / 3) ∧ f3_diff n i j + n / 3 = i) ∨
     (j = n / 2 - 1 + n / 3 ∧ i ≥ 2 * (n / 3) ∧ n = 12 ∧ f3_diff n i j + 7 = i) ∨
     (j = n / 2 - 1 + n / 3 ∧ i ≥ 2 * (n / 3) ∧ n ≥ 18 ∧ f3_diff n i j + n / 3 + 4 = i) ∨
     (n / 2 + n / 3 ≤ j ∧ j ≤ n - 2 ∧ i ≥ n / 3 ∧ f3_diff n i j + 2 * n = i + 2 * j + 1) ∨
     (j ≤ n - 2 ∧ i < n / 3 ∧
      (f3_diff n i j + n = i + 2 * j + 3 ∨ f3_diff n i j + 2 * n = i + 2 * j + 3)) ∨
     (j = n - 1 ∧ (f3_diff n i j = i + 2 ∨ f3_diff n i j + n = i + 2))) := by
  have hq := q3_nat_ge n j hge (by omega) hjlt
  have hv := val_nat_spec n (q3_nat n) i j
  by_cases hjn1 : j = n - 1
  · have hq1 : q3_nat n j = 2 := by rcases hq with ⟨_, hlt, _⟩ | ⟨_, hq1⟩ <;> omega
    have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
      dsimp only [f3_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hjn1, by omega⟩))))⟩
  · have hq1 : q3_nat n j = 2 * (j - (n / 2 - 1)) + 1 := by
      rcases hq with ⟨_, _, hq1⟩ | ⟨hjn, _⟩ <;> omega
    by_cases hik : i < n / 3
    · have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
        dsimp only [f3_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hik, by omega⟩))))⟩
    · by_cases hjm : j = n / 2 - 1 + n / 3
      · by_cases hi2k : i < 2 * (n / 3)
        · have hf : f3_diff n i j = val_nat n (q3_nat n) i j - 1 := by
            dsimp only [f3_diff]; split_ifs <;> omega
          refine ⟨by omega, Or.inl ⟨hjm, by omega, hi2k, by omega⟩⟩
        · by_cases hn12 : n = 12
          · have hf : f3_diff n i j = val_nat n (q3_nat n) i j - 4 := by
              dsimp only [f3_diff]; split_ifs <;> omega
            refine ⟨by omega, Or.inr (Or.inl ⟨hjm, by omega, hn12, by omega⟩)⟩
          · have hf : f3_diff n i j = val_nat n (q3_nat n) i j - 5 := by
              dsimp only [f3_diff]; split_ifs <;> omega
            refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hjm, by omega, by omega, by omega⟩))⟩
      · have hf : f3_diff n i j = val_nat n (q3_nat n) i j - 2 := by
          dsimp only [f3_diff]; split_ifs <;> omega
        refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))⟩

lemma solve_family3 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 0) (hge : n ≥ 12) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  apply exists_incremental_of_nat n h hn (q3_nat n) (f3_sum n) (f3_diff n)
  · intro j hj
    by_cases h1 : j < n / 2 - 1
    · have := q3_nat_lt n j h1; omega
    · have := q3_nat_ge n j hge h1 hj; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 - 1 <;> by_cases h2 : j₂ < n / 2 - 1
    · have := q3_nat_lt n j₁ h1; have := q3_nat_lt n j₂ h2; omega
    · have := q3_nat_lt n j₁ h1; have := q3_nat_ge n j₂ hge h2 hj₂; omega
    · have := q3_nat_ge n j₁ hge h1 hj₁; have := q3_nat_lt n j₂ h2; omega
    · have := q3_nat_ge n j₁ hge h1 hj₁; have := q3_nat_ge n j₂ hge h2 hj₂; omega
  · intro i _ j _; dsimp only [f3_sum]; split_ifs <;> omega
  · intro i _ j _; dsimp only [f3_diff]; split_ifs <;> omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f3_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
      have := f3_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n - 5
      · have := f3_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n - 5
      · have := f3_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n - 5 <;> by_cases h2b : j₂ < n - 5
      · have := f3_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f3_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f3_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
      have := f3_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f3_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_0_spec n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3
      · have := f3_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_0_spec n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3 <;> by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f3_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_1_spec n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f3_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_1_spec n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_2_spec n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_2_spec n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega

/-! ### Small Exceptional Cases: `n ∈ {8, 9, 15, 21}` -/

lemma exists_incremental_of_fin_decide
    (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (q_nat : ℕ → ℕ)
    (f_sum f_diff : ℕ → ℕ → ℕ)
    (h_all :
      (∀ j : Fin n, q_nat j.val < n) ∧
      (∀ j₁ j₂ : Fin n, q_nat j₁.val = q_nat j₂.val → j₁ = j₂) ∧
      (∀ i j : Fin n, f_sum i.val j.val ≤ val_nat n q_nat i.val j.val) ∧
      (∀ i j : Fin n, f_diff i.val j.val ≤ val_nat n q_nat i.val j.val) ∧
      (∀ i₁ j₁ j₂ : Fin n, j₂.val ≤ i₁.val + j₁.val → i₁.val + j₁.val - j₂.val < n →
        f_sum i₁.val j₁.val = f_sum (i₁.val + j₁.val - j₂.val) j₂.val → j₁ = j₂) ∧
      (∀ i₁ j₁ j₂ : Fin n, j₁.val ≤ i₁.val + j₂.val → i₁.val + j₂.val - j₁.val < n →
        f_diff i₁.val j₁.val = f_diff (i₁.val + j₂.val - j₁.val) j₂.val → j₁ = j₂)) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  rcases h_all with ⟨h1, h2, h3, h4, h5, h6⟩
  apply exists_incremental_of_nat n h hn q_nat f_sum f_diff
  · intro j hj; exact h1 ⟨j, hj⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    exact congrArg Fin.val (h2 ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ heq)
  · intro i hi j hj; exact h3 ⟨i, hi⟩ ⟨j, hj⟩
  · intro i hi j hj; exact h4 ⟨i, hi⟩ ⟨j, hj⟩
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    have hi2_eq : i₁ + j₁ - j₂ = i₂ := by omega
    rw [← hi2_eq] at hfeq
    exact congrArg Fin.val (h5 ⟨i₁, hi₁⟩ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (by dsimp only; omega) (by dsimp only; omega) hfeq)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    have hi2_eq : i₁ + j₂ - j₁ = i₂ := by omega
    rw [← hi2_eq] at hfeq
    exact congrArg Fin.val (h6 ⟨i₁, hi₁⟩ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (by dsimp only; omega) (by dsimp only; omega) hfeq)

def q8_nat : ℕ → ℕ
  | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 7 | _ => 5

def f8_sum (i j : ℕ) : ℕ :=
  if j = 3 ∧ i < 4 then i + 1
  else if j = 3 ∧ i = 4 then 3
  else val_nat 8 q8_nat i j

def f8_diff (i j : ℕ) : ℕ :=
  if j = 6 ∧ (i = 5 ∨ i = 6) then i - 5
  else if j = 6 ∧ i = 7 then 5
  else val_nat 8 q8_nat i j

lemma solve_8 (h : 8 > 0) (hn : 8 ≠ 2 ∧ 8 ≠ 3 ∧ 8 ≠ 4 ∧ 8 ≠ 6) :
    ∃ q : Fin 8 → Fin 8, Bijective q ∧ @IsIncremental 8 (@cyclicSquare 8 h hn q) :=
  exists_incremental_of_fin_decide 8 h hn q8_nat f8_sum f8_diff (by decide)

def q9_nat : ℕ → ℕ
  | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 1 | 4 => 8 | 5 => 5 | 6 => 2 | 7 => 4 | _ => 7

def f9_sum (i j : ℕ) : ℕ :=
  if j = 5 ∧ i < 3 then i + 4
  else if j = 5 ∧ i = 3 then 2
  else if j = 6 ∧ i < 2 then i
  else if j = 6 ∧ (i = 2 ∨ i = 3) then 2 * i - 3
  else val_nat 9 q9_nat i j

def f9_diff (i j : ℕ) : ℕ := val_nat 9 q9_nat i j

lemma solve_9 (h : 9 > 0) (hn : 9 ≠ 2 ∧ 9 ≠ 3 ∧ 9 ≠ 4 ∧ 9 ≠ 6) :
    ∃ q : Fin 9 → Fin 9, Bijective q ∧ @IsIncremental 9 (@cyclicSquare 9 h hn q) :=
  exists_incremental_of_fin_decide 9 h hn q9_nat f9_sum f9_diff (by decide)

def q15_nat : ℕ → ℕ
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 9 | 4 => 12
  | 5 => 8 | 6 => 5 | 7 => 2 | 8 => 13 | 9 => 1
  | 10 => 4 | 11 => 7 | 12 => 10 | 13 => 14 | _ => 11

def f15_sum (i j : ℕ) : ℕ := val_nat 15 q15_nat i j

def f15_diff (i j : ℕ) : ℕ :=
  if j = 13 ∧ i = 10 then 5
  else if j = 13 ∧ 11 ≤ i ∧ i ≤ 14 then i - 8
  else if j = 14 ∧ (i = 5 ∨ i = 6) then i - 5
  else if j = 14 ∧ 7 ≤ i ∧ i ≤ 10 then i - 6
  else if j = 14 ∧ (i = 11 ∨ i = 12 ∨ i = 14) then 2
  else if j = 14 ∧ i = 13 then 1
  else val_nat 15 q15_nat i j

lemma solve_15 (h : 15 > 0) (hn : 15 ≠ 2 ∧ 15 ≠ 3 ∧ 15 ≠ 4 ∧ 15 ≠ 6) :
    ∃ q : Fin 15 → Fin 15, Bijective q ∧ @IsIncremental 15 (@cyclicSquare 15 h hn q) :=
  exists_incremental_of_fin_decide 15 h hn q15_nat f15_sum f15_diff (by decide)

def q21_nat : ℕ → ℕ
  | 0 => 0 | 1 => 18 | 2 => 15 | 3 => 12 | 4 => 9 | 5 => 6 | 6 => 3
  | 7 => 7 | 8 => 4 | 9 => 1 | 10 => 14 | 11 => 17 | 12 => 10 | 13 => 16
  | 14 => 2 | 15 => 5 | 16 => 11 | 17 => 8 | 18 => 20 | 19 => 13 | _ => 19

def f21_sum (i j : ℕ) : ℕ :=
  if j = 7 ∧ i ≤ 12 then i + 6
  else if j = 7 ∧ i = 13 then 13
  else if j = 8 ∧ i ≤ 7 then i + 3
  else if j = 8 ∧ 8 ≤ i ∧ i ≤ 10 then i + 2
  else if j = 8 ∧ (i = 11 ∨ i = 13) then i + 1
  else if j = 8 ∧ i = 12 then 9
  else if j = 9 ∧ i ≤ 7 then i
  else if j = 9 ∧ (i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 12 ∨ i = 13) then i - 2
  else if j = 9 ∧ i = 11 then 7
  else if j = 14 ∧ i ≤ 5 then i + 1
  else if j = 14 ∧ i = 6 then 6
  else if j = 14 ∧ 7 ≤ i ∧ i ≤ 9 then i + 1
  else val_nat 21 q21_nat i j

def f21_diff (i j : ℕ) : ℕ :=
  if j = 18 ∧ 16 ≤ i ∧ i ≤ 20 then i - 13
  else if j = 19 ∧ 14 ≤ i ∧ i ≤ 16 then i - 14
  else if j = 19 ∧ 17 ≤ i ∧ i ≤ 20 then i - 17
  else val_nat 21 q21_nat i j

lemma solve_21 (h : 21 > 0) (hn : 21 ≠ 2 ∧ 21 ≠ 3 ∧ 21 ≠ 4 ∧ 21 ≠ 6) :
    ∃ q : Fin 21 → Fin 21, Bijective q ∧ @IsIncremental 21 (@cyclicSquare 21 h hn q) :=
  exists_incremental_of_fin_decide 21 h hn q21_nat f21_sum f21_diff (by decide)

/-! ### Main Theorem -/

theorem Conjecture :
  ∀ (n : ℕ)
    (h : n > 0)
    (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6),
  ∃ q : Fin n → Fin n,
        Bijective q
      ∧ @IsIncremental n (@cyclicSquare n h hn q) := by
  intro n h hn
  have hmod :
      (n % 6 = 1 ∨ n % 6 = 5) ∨
      ((n % 6 = 2 ∨ n % 6 = 4) ∧ (n = 8 ∨ n ≥ 10)) ∨
      (n % 6 = 0 ∧ n ≥ 12) ∨
      (n % 6 = 3 ∧ (n = 9 ∨ n = 15 ∨ n = 21 ∨ n ≥ 27)) := by omega
  rcases hmod with h1 | ⟨h2, rfl | hge⟩ | ⟨h3, hge⟩ | ⟨h4, rfl | rfl | rfl | hge⟩
  · exact solve_family1 n h hn h1
  · exact solve_8 h hn
  · exact solve_family2 n h hn h2 hge
  · exact solve_family3 n h hn h3 hge
  · exact solve_9 h hn
  · exact solve_15 h hn
  · exact solve_21 h hn
  · exact solve_family4 n h hn h4 hge

-------------------------------------------------------------------------------

-- /-
-- ### Diagnostics and Testing
-- Testing the conjecture by explicitly checking candidate permutations
-- `q : Fin n → Fin n` and exhaustively searching through all bijections.
-- -/

-- /-- Checks whether `q : Fin n → Fin n` satisfies the diagonal threshold
--     bounds. Returns `none` if valid, or `some "Failure"`. -/
-- def failure
--   (n : ℕ)
--   (h : n > 0 := by omega)
--   (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6 := by omega)
--   (q : Fin n → Fin n) :
--  Option String := Id.run do
--   let L := cyclicSquare n h hn q
--   for k in [0:n] do
--     -- Check all 2n - 1 anti-diagonals s ∈ [0, 2n - 2]
--     for s in [0 : 2 * n - 1] do
--       let cnt := #(sumDiagOk n s k L)
--       if cnt > k + 1 then
--         return some "Failure"
--     -- Check all 2n - 1 main diagonals d ∈ [-(n-1), n-1]
--     for d' in [0 : 2 * n - 1] do
--       let d : ℤ := (d' : ℤ) - ((n : ℤ) - 1)
--       let cnt := #(diffDiagOk n d k L)
--       if cnt > k + 1 then
--         return some "Failure"
--   return none

-- /-- Renders the n × n Latin square as a grid of numbers for visual
-- inspection. -/
-- def formatSquare
--   (n : ℕ)
--   (h : n > 0 := by omega)
--   (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6 := by omega)
--   (q : Fin n → Fin n) : String := Id.run do
--   let L := cyclicSquare n h hn q
--   let mut res := s!"--- {n}×{n} Latin Square ---\n"
--   for i in [0:n] do
--     let mut row := ""
--     for j in [0:n] do
--       let val := (L ⟨i % n, mod_lt _ h⟩ ⟨j % n, mod_lt _ h⟩).val
--       row := row ++ s!"{val} "
--     res := res ++ row ++ "\n"
--   return res

-- /-- Generate all n! bijections of `Fin n` and find the first valid one. -/
-- def testAllBijections
--   (n : ℕ)
--   (h : n > 0 := by omega)
--   (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6 := by omega) : String := Id.run do
--   let allPermLists := (List.range n).permutations
--   let total := allPermLists.length
--   for l in allPermLists do
--     let q : Fin n → Fin n := fun j => ⟨(l.getD j.val 0) % n, mod_lt _ h⟩
--     if (failure n h hn q).isNone then
--       let qList :=
--         (List.range n).map (fun j => (q ⟨j % n, mod_lt _ h⟩).val)
--       return s!"n = {n}\nSUCCESS\nFound valid bijection\nq = {qList}\n"
--             ++ s!"out of {total} permutations.\n"
--              ++ formatSquare n h hn q
--   return s!"n = {n}\nFAILED\nExhausted all {total} permutations.\n"

-- #eval IO.println (testAllBijections 9)

end IncrementalCyclic
