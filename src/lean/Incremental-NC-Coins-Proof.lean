-- cfr. https://puzzling.stackexchange.com/questions/138939

import Mathlib

namespace IncrementalCyclic

open Function (Bijective)
open Nat (mod_lt)
open Finset (univ)

open scoped Finset

-- Given a natural number `n : ℕ` and a function `q : Fin n → Fin n`,
-- the function `cyclicSquare` of type `Fin n → Fin n → Fin n`
-- encodes a cyclic nxn square.
-- Notice that `q` does not need to be a bijection
-- but it will be required to a bejection in `IsIncremental` below.
def cyclicSquare
    (n : ℕ)
    (q : Fin n → Fin n)
    (h : n > 0)
    (_ : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6) :
  Fin n → Fin n → Fin n :=

    fun i j =>
      ⟨(i.val + (q j).val) % n, mod_lt _ h⟩

-- Cells on a diagonal of constant `s` (row + column), with value at most `k`.
def sumDiagOk
    (n : ℕ)
    (s : ℕ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun p : Fin n × Fin n =>
        p.1.val + p.2.val = s
      ∧ (L p.1 p.2).val ≤ k

-- Cells on a diagonal of constant `d` (row - column), with value at most `k`.
def diffDiagOk
    (n : ℕ)
    (d : ℤ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun p : Fin n × Fin n =>
        ((p.1.val : ℤ) - (p.2.val : ℤ)) = d
      ∧ (L p.1 p.2).val ≤ k

-- Every threshold square has at most `k+1` cells on each diagonal,
-- for every threshold `k < n`.
def IsIncremental
    (n : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Prop :=

        (∀ i : Fin n, Bijective (L i .))
      ∧ (∀ j : Fin n, Bijective (L . j))
    ∧ ∀ k : ℕ,
        k < n →
          (∀ s : ℕ, #(sumDiagOk  n s k L) ≤ k + 1)
        ∧ (∀ d : ℤ, #(diffDiagOk n d k L) ≤ k + 1)

/-- Conditional-subtraction form of `(i + q_nat j) % n` for `i < n` and `q_nat j < n`. -/
def val_nat (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) : ℕ :=
  if i + q_nat j < n then i + q_nat j else i + q_nat j - n

/-- This lemma justifies using pure Presburger arithmetic (linear integer inequalities),
    which Lean's `omega` tactic can decide directly -/
lemma mod_eq_val_nat (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) (hi : i < n) (hq : q_nat j < n) :
    (i + q_nat j) % n = val_nat n q_nat i j := by
  dsimp only [val_nat]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have h1 : n ≤ i + q_nat j := by omega
    have h2 : i + q_nat j - n < n := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]

/-- This lemma deals with the two possibilities for `i + q_nat j` -/
lemma val_nat_prop (n : ℕ) (q_nat : ℕ → ℕ) (i j : ℕ) :
    (i + q_nat j < n ∧ val_nat n q_nat i j = i + q_nat j) ∨
    (i + q_nat j ≥ n ∧ val_nat n q_nat i j = i + q_nat j - n) := by
  dsimp only [val_nat]; split_ifs <;> omega

/-- **The Injective-Majorization Reduction:**
    If `q_nat` is a permutation of `{0, ..., n-1}` and `f_sum, f_diff ≤ val_nat n q_nat` are
    injective along every sum-diagonal and difference-diagonal respectively, then the Latin square
    `cyclicSquare n q h hn` is incremental (`IsIncremental`). -/
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
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
  let q : Fin n → Fin n := fun j => ⟨q_nat j.val, hq_lt j.val j.isLt⟩
  have hq_bij : Bijective q := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun j₁ j₂ heq => ?_, rfl⟩
    apply Fin.ext
    exact hq_inj j₁.val j₁.isLt j₂.val j₂.isLt (congrArg Fin.val heq)
  have hL_val : ∀ i j : Fin n, (cyclicSquare n q h hn i j).val
         = val_nat n q_nat i.val j.val := by
    intro i j
    exact mod_eq_val_nat n q_nat i.val j.val i.isLt (hq_lt j.val j.isLt)
  refine ⟨q, hq_bij, ?_, ?_, ?_⟩
  -- Row bijectivity: `j ↦ (i + q(j)) % n` is injective because `q` is injective
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
    have hv1 := val_nat_prop n q_nat i.val j₁.val
    have hv2 := val_nat_prop n q_nat i.val j₂.val
    have hq_eq : q_nat j₁.val = q_nat j₂.val := by omega
    exact Fin.ext (hq_inj j₁.val j₁.isLt j₂.val j₂.isLt hq_eq)
  -- Column bijectivity: `i ↦ (i + q(j)) % n` is a cyclic shift of `Fin n`
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
    have hv1 := val_nat_prop n q_nat i₁.val j.val
    have hv2 := val_nat_prop n q_nat i₂.val j.val
    apply Fin.ext
    omega
  -- Diagonal threshold bounds via Pigeonhole Principle (`Finset.card_le_card_of_injOn`)
  · intro k _hk
    refine ⟨fun s => ?_, fun d => ?_⟩
    -- Sum-diagonal `i + j = s`: `f_sum` maps `sumDiagOk` injectively into `range (k + 1)`
    · calc #(sumDiagOk n s k (cyclicSquare n q h hn))
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
    -- Diff-diagonal `i - j = d`: `f_diff` maps `diffDiagOk` injectively into `range (k + 1)`
    · calc #(diffDiagOk n d k (cyclicSquare n q h hn))
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

/-!
### Family 1: `n ≡ 1, 5 (mod 6)` (`n ≥ 1`)

When `gcd(n, 6) = 1`, the pure linear permutation `q₁(j) = (-2j) mod n` has:
- Column step `-2 mod n`, which is bijective since `gcd(2, n) = 1`.
- Sum-diagonal step (`i + j = s ⇒ i = s - j`): `(s - j) - 2j = s - 3j mod n`, which is
  already injective on every sum-diagonal since `gcd(3, n) = 1`!
- Diff-diagonal step (`i - j = d ⇒ i = d + j`): `(d + j) - 2j = d - j mod n`, which has
  step `-1 mod n` and is trivially injective on every diff-diagonal!

Because there are no diagonal collisions at all, no downward shifts are needed:
we take `f_sum = val_nat` and `f_diff = val_nat`.
-/

/-- `q₁(j) = (-2j) mod n`, written without `% n` as three linear branches. -/
def q1_nat (n j : ℕ) : ℕ :=
  if j = 0 then 0
  else if 2 * j < n then n - 2 * j
  else 2 * n - 2 * j

lemma q1_nat_prop (n j : ℕ) :
    (j = 0 ∧ q1_nat n j = 0) ∨
    (j > 0 ∧ 2 * j < n ∧ q1_nat n j = n - 2 * j) ∨
    (j > 0 ∧ 2 * j ≥ n ∧ q1_nat n j = 2 * n - 2 * j) := by
  dsimp only [q1_nat]; split_ifs <;> omega

lemma solve_family1 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
  apply exists_incremental_of_nat n h hn
    -- with
    (q1_nat n) (val_nat n (q1_nat n)) (val_nat n (q1_nat n))
  -- 1. `q₁(j) < n`
  · intro j hj; have := q1_nat_prop n j; omega
  -- 2. `q₁` is injective: `2(j₂ - j₁) = k * n` with `0 ≤ j₁, j₂ < n` forces `j₁ = j₂`
  --    because `hmod : n % 6 = 1 ∨ n % 6 = 5` implies `n` is odd (`2 ∤ n`).
  · intro j₁ hj₁ j₂ hj₂ heq
    have := q1_nat_prop n j₁; have := q1_nat_prop n j₂; omega
  -- 3. `f_sum ≤ val_nat` (trivial since `f_sum = val_nat`)
  · intro i _ j _; exact le_rfl
  -- 4. `f_diff ≤ val_nat` (trivial since `f_diff = val_nat`)
  · intro i _ j _; exact le_rfl
  -- 5. Sum-diagonal injectivity: along `i₁ + j₁ = i₂ + j₂`, `v(i₁, j₁) = v(i₂, j₂)`
  --    gives `3(j₂ - j₁) = k * n`. Here `omega` uses `hmod` (`3 ∤ n`) to deduce `j₁ = j₂`.
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    have := q1_nat_prop n j₁; have := q1_nat_prop n j₂
    have := val_nat_prop n (q1_nat n) i₁ j₁; have := val_nat_prop n (q1_nat n) i₂ j₂
    omega
  -- 6. Diff-diagonal injectivity: along `i₁ - j₁ = i₂ - j₂`, `v(i₁, j₁) = v(i₂, j₂)`
  --    gives `(j₂ - j₁) = k * n`, which immediately forces `j₁ = j₂`.
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    have := q1_nat_prop n j₁; have := q1_nat_prop n j₂
    have := val_nat_prop n (q1_nat n) i₁ j₁; have := val_nat_prop n (q1_nat n) i₂ j₂
    omega

/-!
### Family 2: `n ≡ 2, 4 (mod 6)`, `n ≥ 10`

For even `n` not divisible by `3`, let `m = n / 2`. We split the columns into two halves of
length `m` with step `+2` inside each half and a parity-switching jump of `+3` at `j = m`:
- For `0 ≤ j < m`: `q₂(j) = (2j + m + 1) mod n` (covers all residues of parity `(m + 1) mod 2`).
- For `m ≤ j < n`: `q₂(j) = (2(j - m) + m + 4) mod n ≡ (2j + m + 4) mod n`
  (covers all residues of the opposite parity `(m + 4) mod 2`).

**Where collisions occur and how `f2_sum` and `f2_diff` resolve them:**
- **Sum-diagonals (`i + j = s`):** Inside each half, `i + q₂(j) = (s - j) + 2j + ...` has step `+1`.
  Because the second half is shifted by `+3 mod n`, a collision between `j₁ < m ≤ j₂`
  satisfies `(j₂ - j₁) + 3 = n ⇔ j₂ - j₁ = n - 3`. This happens ONLY when `j₁ ∈ {0, 1, 2}` and
  `j₂ ∈ {n - 3, n - 2, n - 1}` with `i₂ < 3` (the **3×3 top-right corner**).
  `f2_sum` shifts those 9 corner cells down to `j - (n - 3) ∈ {0, 1, 2}`, which are vacant on those
  sum-diagonals.
- **Diff-diagonals (`i - j = d`):** Inside each half, `i + q₂(j) = (d + j) + 2j + ...` has step `+3`.
  Since `gcd(3, n) = 1` (from `hmod : n % 6 = 2 ∨ n % 6 = 4`), a collision between `j₁ < m ≤ j₂`
  satisfies `3(j₂ - j₁) + 3 ≡ 0 (mod n) ⇔ j₂ - j₁ = n - 1`. This happens ONLY at a **single pair
  of cells on the entire board**: `(0, 0)` and `(n - 1, n - 1)` on the main diagonal `d = 0`.
  `f2_diff` shifts the bottom-right cell `(n - 1, n - 1)` down to `1`, which is vacant on `d = 0`.
-/

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

/-- Sum-diagonal majorant for Family 2: shifts the 3×3 top-right corner `i < 3 ∧ j ≥ n - 3`
    down to `j - (n - 3) ∈ {0, 1, 2}`. -/
def f2_sum (n i j : ℕ) : ℕ :=
  if i < 3 ∧ j ≥ n - 3 then j - (n - 3) else val_nat n (q2_nat n) i j

/-- Diff-diagonal majorant for Family 2: shifts the single bottom-right corner cell
    `(n - 1, n - 1)` down from `n / 2 + 1` to `1`. -/
def f2_diff (n i j : ℕ) : ℕ :=
  if i = n - 1 ∧ j = n - 1 then 1 else val_nat n (q2_nat n) i j

/-- Flat linear property of `f2_sum` on the first half `j < n / 2`. -/
lemma f2_sum_lt_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_sum n i j ≤ val_nat n (q2_nat n) i j ∧ f2_sum n i j < n ∧
    (f2_sum n i j = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hq := q2_nat_lt n j hj
  have hv := val_nat_prop n (q2_nat n) i j
  have hf : f2_sum n i j = val_nat n (q2_nat n) i j := by
    dsimp only [f2_sum]; split_ifs <;> omega
  omega

/-- Flat linear property of `f2_sum` on the second half `j ≥ n / 2`. -/
lemma f2_sum_ge_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_sum n i j ≤ val_nat n (q2_nat n) i j ∧ f2_sum n i j < n ∧
    ((i < 3 ∧ j ≥ n - 3 ∧ f2_sum n i j = j - (n - 3)) ∨
     ((i ≥ 3 ∨ j < n - 3) ∧
      (f2_sum n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hq := q2_nat_ge n j hjge
  have hv := val_nat_prop n (q2_nat n) i j
  dsimp only [f2_sum]; split_ifs <;> omega

/-- Flat linear property of `f2_diff` on the first half `j < n / 2`. -/
lemma f2_diff_lt_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_diff n i j ≤ val_nat n (q2_nat n) i j ∧ f2_diff n i j < n ∧
    (f2_diff n i j = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hq := q2_nat_lt n j hj
  have hv := val_nat_prop n (q2_nat n) i j
  have hf : f2_diff n i j = val_nat n (q2_nat n) i j := by
    dsimp only [f2_diff]; split_ifs <;> omega
  omega

/-- Flat linear property of `f2_diff` on the second half `j ≥ n / 2`. -/
lemma f2_diff_ge_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_diff n i j ≤ val_nat n (q2_nat n) i j ∧ f2_diff n i j < n ∧
    ((i = n - 1 ∧ j = n - 1 ∧ f2_diff n i j = 1) ∨
     (i + j < 2 * n - 2 ∧
      (f2_diff n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hq := q2_nat_ge n j hjge
  have hv := val_nat_prop n (q2_nat n) i j
  dsimp only [f2_diff]; split_ifs <;> omega

lemma solve_family2 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 2 ∨ n % 6 = 4) (hge : n ≥ 10) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
  have heven : n % 2 = 0 := by omega
  apply exists_incremental_of_nat n h hn
  -- with
    (q2_nat n) (f2_sum n) (f2_diff n)
  -- 1. `q₂(j) < n`
  · intro j hj
    by_cases h1 : j < n / 2
    · have := q2_nat_lt n j h1; omega
    · have := q2_nat_ge n j h1; omega
  -- 2. `q₂` is injective: the two halves have opposite parities `(n/2 + 1)` vs `(n/2 + 4)`
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := q2_nat_lt n j₁ h1; have := q2_nat_lt n j₂ h2; omega
    · have := q2_nat_lt n j₁ h1; have := q2_nat_ge n j₂ h2; omega
    · have := q2_nat_ge n j₁ h1; have := q2_nat_lt n j₂ h2; omega
    · have := q2_nat_ge n j₁ h1; have := q2_nat_ge n j₂ h2; omega
  -- 3. `f2_sum ≤ val_nat`
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_sum_lt_prop n i j hge heven hi h1).1
    · exact (f2_sum_ge_prop n i j hge heven hi hj h1).1
  -- 4. `f2_diff ≤ val_nat`
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_diff_lt_prop n i j hge heven hi h1).1
    · exact (f2_diff_ge_prop n i j hge heven hi hj h1).1
  -- 5. Sum-diagonal injectivity of `f2_sum` across the 2×2 half-board combinations
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_sum_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_sum_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
  -- 6. Diff-diagonal injectivity of `f2_diff` (uses `hmod : n % 6 = 2 ∨ n % 6 = 4` so `3 ∤ n`)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_diff_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_diff_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega

/-!
### Family 4: `n ≡ 3 (mod 6)`, `n ≥ 27`

When `n ≡ 3 (mod 6)`, `n` is odd and divisible by `3`. Let `k = n / 3`.
Because `n` is odd, a column step of `+3` gives:
- Sum-diagonal step `3 - 1 = +2` (`gcd(2, n) = 1`), and
- Diff-diagonal step `3 + 1 = +4` (`gcd(4, n) = 1`)!

We partition `{0, ..., n - 1}` into three blocks of length `k` (`u = j / k ∈ {0, 1, 2}`),
with a `+4` jump between consecutive blocks so that all three residue classes mod `3` are covered:
`q₄(j) = (3j + 2k + 4u) mod n`.
(The threshold `n ≥ 27`, i.e. `k ≥ 9`, ensures `2k + 8 < 3k = n` at the start of the third block.)

**Where collisions occur and how `f4_sum` and `f4_diff` resolve them:**
- **Sum-diagonals (`i + j = s`):** Collisions between block `u₁` and block `u₂` satisfy
  `2(j₂ - j₁) + 4(u₂ - u₁) ≡ 0 (mod n) ⇔ (j₂ - j₁) + 2(u₂ - u₁) = n` (since `n` is odd).
  This requires `u₁ = 0, u₂ = 2` and `j₂ - j₁ = n - 4`, which ONLY occurs in the **4×4 top-right
  corner** `i < 4 ∧ j ≥ n - 4`. `f4_sum` shifts those 16 cells down by `k` or `2k`.
- **Diff-diagonals (`i - j = d`):** Collisions satisfy `4(j₂ - j₁) + 4(u₂ - u₁) ≡ 0 (mod n) ⇔
  (j₂ - j₁) + (u₂ - u₁) = n` (since `gcd(4, n) = 1`). This requires `u₁ = 0, u₂ = 2` and
  `j₂ - j₁ = n - 2`, which ONLY occurs in the **2×2 bottom-right corner** `i ≥ n - 2 ∧ j ≥ n - 2`.
  `f4_diff` shifts those 4 cells down by `2k` (for `j = n - 2`) and `k` (for `j = n - 1`).
-/

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

/-- Sum-diagonal majorant for Family 4: shifts the 4×4 top-right corner `i < 4 ∧ j ≥ n - 4`
    by `-k` (for `j ∈ {n-4, n-3}`) or `-2k` (for `j ∈ {n-2, n-1}`). -/
def f4_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (q4_nat n) i j
  let k := n / 3
  if i < 4 ∧ (j = n - 4 ∨ j = n - 3) then v - k
  else if i < 4 ∧ (j = n - 2 ∨ j = n - 1) then v - 2 * k
  else v

/-- Diff-diagonal majorant for Family 4: shifts the 2×2 bottom-right corner `i ≥ n - 2 ∧ j ≥ n - 2`
    by `-2k` (at `j = n - 2`) or `-k` (at `j = n - 1`). -/
def f4_diff (n i j : ℕ) : ℕ :=
  let v := val_nat n (q4_nat n) i j
  let k := n / 3
  if i ≥ n - 2 ∧ j = n - 2 then v - 2 * k
  else if i ≥ n - 2 ∧ j = n - 1 then v - k
  else v

lemma f4_sum_0_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f4_sum n i j < n ∧
    (f4_sum n i j = i + 3 * j + 2 * (n / 3) ∨
     f4_sum n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hq := q4_nat_0 n j hj
  have hv := val_nat_prop n (q4_nat n) i j
  have hf : f4_sum n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_sum]; split_ifs <;> omega
  omega

lemma f4_sum_1_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f4_sum n i j < n ∧
    (f4_sum n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hq := q4_nat_1 n j hj1 hj2
  have hv := val_nat_prop n (q4_nat n) i j
  have hf : f4_sum n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_sum]; split_ifs <;> omega
  omega

lemma f4_sum_2_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f4_sum n i j < n ∧
    ((i < 4 ∧ (j = n - 4 ∨ j = n - 3) ∧ f4_sum n i j + 3 * n = i + 3 * j + n / 3 + 8) ∨
     (i < 4 ∧ (j = n - 2 ∨ j = n - 1) ∧ f4_sum n i j + 3 * n = i + 3 * j + 8) ∨
     ((i ≥ 4 ∨ j < n - 4) ∧
      (f4_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_sum n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hq := q4_nat_2 n j hj1 hj2
  have hv := val_nat_prop n (q4_nat n) i j
  dsimp only [f4_sum]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma f4_diff_0_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f4_diff n i j < n ∧
    (f4_diff n i j = i + 3 * j + 2 * (n / 3) ∨
     f4_diff n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hq := q4_nat_0 n j hj
  have hv := val_nat_prop n (q4_nat n) i j
  have hf : f4_diff n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_diff]; split_ifs <;> omega
  omega

lemma f4_diff_1_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f4_diff n i j < n ∧
    (f4_diff n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f4_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hq := q4_nat_1 n j hj1 hj2
  have hv := val_nat_prop n (q4_nat n) i j
  have hf : f4_diff n i j = val_nat n (q4_nat n) i j := by
    dsimp only [f4_diff]; split_ifs <;> omega
  omega

lemma f4_diff_2_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f4_diff n i j < n ∧
    ((i ≥ n - 2 ∧ j = n - 2 ∧ f4_diff n i j + n = i + 2) ∨
     (i ≥ n - 2 ∧ j = n - 1 ∧ f4_diff n i j + 2 * (n / 3) = i + 5) ∨
     ((i < n - 2 ∨ j < n - 2) ∧
      (f4_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f4_diff n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hq := q4_nat_2 n j hj1 hj2
  have hv := val_nat_prop n (q4_nat n) i j
  dsimp only [f4_diff]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma solve_family4 (n : ℕ) (h : n > 0) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 3) (hge : n ≥ 27) :
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
  apply exists_incremental_of_nat n h hn
  -- with
    (q4_nat n) (f4_sum n) (f4_diff n)
  -- 1. `q₄(j) < n` across the 3 blocks
  · intro j hj
    by_cases h1 : j < n / 3
    · have := q4_nat_0 n j h1; omega
    · by_cases h2 : j < 2 * (n / 3)
      · have := q4_nat_1 n j h1 h2; omega
      · have := q4_nat_2 n j h1 h2; omega
  -- 2. `q₄` is injective: the 3 blocks have distinct residues mod 3 (`2k`, `2k+4`, `2k+8`)
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
  -- 3. `f4_sum ≤ val_nat` (since `f4_sum` only subtracts `k` or `2k`)
  · intro i _ j _; dsimp only [f4_sum]; split_ifs <;> omega
  -- 4. `f4_diff ≤ val_nat` (since `f4_diff` only subtracts `k` or `2k`)
  · intro i _ j _; dsimp only [f4_diff]; split_ifs <;> omega
  -- 5. Sum-diagonal injectivity of `f4_sum` across all 3×3 block pairs (uses `hmod : n % 6 = 3` so ``gcd(2, n) = 1``)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
  -- 6. Diff-diagonal injectivity of `f4_diff` across all 3×3 block pairs (uses `hmod : n % 6 = 3` so `gcd(4, n) = 1`)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega

/-!
### Family 3: `n ≡ 0 (mod 6)`, `n ≥ 12`

When `6 ∣ n`, both `2 ∣ n` and `3 ∣ n`. Let `m = n / 2` and `k = n / 3`.
We define a 5-piece column permutation `q₃`:
- Three boundary pins `j = 0 ↦ n - 2`, `j = m - 2 ↦ 0`, `j = n - 1 ↦ 2` covering `{0, 2, n - 2}`.
- First main block `1 ≤ j ≤ m - 3`: `q₃(j) = 2j + 2` (covers `{4, 6, ..., n - 4}`).
- Second main block `m - 1 ≤ j ≤ n - 2`: `q₃(j) = 2(j - (m - 1)) + 1` (covers all odd numbers `{1, 3, ..., n - 1}`).

**Why this works on both diagonals:**
- **Sum-diagonals (`i + j = s`):** Inside both main blocks, `i + q₃(j)` has step `+1`, so values
  are almost completely distinct; collisions ONLY occur at the seams `j = m - 1`, `j = n - 5`
  (when `i + j < n`), and `j = n - 1` (when `i < 2`), which `f3_sum` shifts downward.
- **Diff-diagonals (`i - j = d`):** Inside both main blocks, `i + q₃(j) = (d + j) + 2j + ...`
  has step `+3`! Since `3 ∣ n`, the first main block stays entirely in residue class `d + 2 (mod 3)`
  and the second main block stays entirely in residue class `d (mod 3)`, **leaving the third
  residue class `d + 1 (mod 3)` completely vacant** (except for the single pin `j = 0`).
  When either main block wraps around `n` (at `j₂ - j₁ = n / 3 = k`), `f3_diff` shifts the wrapped
  cells in the first block down by `-1` and in the second block down by `-2` (with boundary tweaks
  at `j = m - 1 + k`), landing them injectively inside the vacant residue class `d + 1 (mod 3)`!
-/

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

/-- Sum-diagonal majorant for Family 3: shifts only at the three seam columns
    `j = m - 1`, `j = n - 5` (for `i + j < n`), and `j = n - 1` (for `i < 2`). -/
def f3_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (q3_nat n) i j
  let m := n / 2
  if j = m - 1 ∧ i < n - 1 then v - 1
  else if j = n - 5 ∧ i + j < n then v - (m - 2)
  else if j = n - 1 ∧ i < 2 then v - 1
  else v

/-- Diff-diagonal majorant for Family 3: shifts the wrapped portions (`j ≥ 1 + k` in block 1
    and `j ≥ m - 1 + k` in block 2, for `i ≥ k`) into the vacant residue class `d + 1 (mod 3)`. -/
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

lemma f3_sum_0_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f3_sum n i j < n ∧
    ((j = 0 ∧ (f3_sum n i j = i + n - 2 ∨ f3_sum n i j + 2 = i)) ∨
     (1 ≤ j ∧ j < n / 2 - 2 ∧ (f3_sum n i j = i + 2 * j + 2 ∨ f3_sum n i j + n = i + 2 * j + 2)) ∨
     (j = n / 2 - 2 ∧ f3_sum n i j = i)) := by
  have hq := q3_nat_lt n j hj
  have hv := val_nat_prop n (q3_nat n) i j
  have hf : f3_sum n i j = val_nat n (q3_nat n) i j := by
    dsimp only [f3_sum]; split_ifs <;> omega
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine ⟨by omega, Or.inl ⟨h1, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h1, h2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨h1, by omega⟩)⟩

lemma f3_sum_1_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n - 5) :
    f3_sum n i j < n ∧
    ((j = n / 2 - 1 ∧ i < n - 1 ∧ f3_sum n i j = i) ∨
     (j = n / 2 - 1 ∧ i = n - 1 ∧ f3_sum n i j = 0) ∨
     (n / 2 ≤ j ∧ j < n - 5 ∧
      (f3_sum n i j + n = i + 2 * j + 3 ∨ f3_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hq := q3_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_prop n (q3_nat n) i j
  dsimp only [f3_sum]
  split_ifs with hs1 hs2 hs3
  · refine ⟨by omega, Or.inl ⟨hs1.1, hs1.2, by omega⟩⟩
  · omega
  · omega
  · by_cases hjm : j = n / 2 - 1
    · refine ⟨by omega, Or.inr (Or.inl ⟨hjm, by omega, by omega⟩)⟩
    · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, hj2, by omega⟩)⟩

lemma f3_sum_2_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
    (hj2 : ¬ j < n - 5) :
    f3_sum n i j < n ∧
    ((j = n - 5 ∧ i < 5 ∧ f3_sum n i j = i + n / 2 - 5) ∨
     (j = n - 1 ∧ i < 2 ∧ f3_sum n i j = i + 1) ∨
     (j = n - 1 ∧ i ≥ 2 ∧ (f3_sum n i j = i + 2 ∨ f3_sum n i j + n = i + 2)) ∨
     (j < n - 1 ∧ (j ≠ n - 5 ∨ i ≥ 5) ∧
      (f3_sum n i j + n = i + 2 * j + 3 ∨ f3_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hq := q3_nat_ge n j hge (by omega) hjlt
  have hv := val_nat_prop n (q3_nat n) i j
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

lemma f3_diff_0_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f3_diff n i j < n ∧
    ((j = 0 ∧ (f3_diff n i j = i + n - 2 ∨ f3_diff n i j + 2 = i)) ∨
     (j = n / 2 - 2 ∧ f3_diff n i j = i) ∨
     (1 + n / 3 ≤ j ∧ j ≤ n / 2 - 3 ∧ i ≥ n / 3 ∧ f3_diff n i j + n = i + 2 * j + 1) ∨
     (1 ≤ j ∧ j ≤ n / 2 - 3 ∧ (j < 1 + n / 3 ∨ i < n / 3) ∧
      (f3_diff n i j = i + 2 * j + 2 ∨ f3_diff n i j + n = i + 2 * j + 2))) := by
  have hq := q3_nat_lt n j hj
  have hv := val_nat_prop n (q3_nat n) i j
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

lemma f3_diff_1_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n / 2 - 1 + n / 3) :
    f3_diff n i j < n ∧
    (f3_diff n i j + n = i + 2 * j + 3 ∨ f3_diff n i j + 2 * n = i + 2 * j + 3) := by
  have hq := q3_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_prop n (q3_nat n) i j
  have hf : f3_diff n i j = val_nat n (q3_nat n) i j := by
    dsimp only [f3_diff]; split_ifs <;> omega
  rcases hq with ⟨_, _, hq1⟩ | ⟨hjn, _⟩ <;> omega

lemma f3_diff_2_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
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
  have hv := val_nat_prop n (q3_nat n) i j
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
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
  apply exists_incremental_of_nat n h hn
  -- with
    (q3_nat n) (f3_sum n) (f3_diff n)
  -- 1. `q₃(j) < n`
  · intro j hj
    by_cases h1 : j < n / 2 - 1
    · have := q3_nat_lt n j h1; omega
    · have := q3_nat_ge n j hge h1 hj; omega
  -- 2. `q₃` is injective: `{0, m-2, n-1} ∪ [1, m-3]` covers all even residues,
  --    and `[m-1, n-2]` covers all odd residues.
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 - 1 <;> by_cases h2 : j₂ < n / 2 - 1
    · have := q3_nat_lt n j₁ h1; have := q3_nat_lt n j₂ h2; omega
    · have := q3_nat_lt n j₁ h1; have := q3_nat_ge n j₂ hge h2 hj₂; omega
    · have := q3_nat_ge n j₁ hge h1 hj₁; have := q3_nat_lt n j₂ h2; omega
    · have := q3_nat_ge n j₁ hge h1 hj₁; have := q3_nat_ge n j₂ hge h2 hj₂; omega
  -- 3. `f3_sum ≤ val_nat`
  · intro i _ j _; dsimp only [f3_sum]; split_ifs <;> omega
  -- 4. `f3_diff ≤ val_nat`
  · intro i _ j _; dsimp only [f3_diff]; split_ifs <;> omega
  -- 5. Sum-diagonal injectivity of `f3_sum` across the 3×3 column regions
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n - 5
      · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n - 5
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n - 5 <;> by_cases h2b : j₂ < n - 5
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
  -- 6. Diff-diagonal injectivity of `f3_diff` across the 3×3 column regions:
  --    `omega` uses `hmod : n % 6 = 0` to distinguish the three mod-3 residue classes
  --    `d + 2 (mod 3)`, `d (mod 3)`, and `d + 1 (mod 3)`.
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3 <;> by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega

/-!
### Small Exceptional Cases: `n ∈ {8, 9, 15, 21}`

The four infinite families cover all `n ∉ {2, 3, 4, 6}` except `n = 8` (below the `n ≥ 10`
threshold of Family 2) and `n ∈ {9, 15, 21}` (below the `n ≥ 27` threshold of Family 4).
For these four concrete dimensions, `exists_incremental_of_fin_decide` eliminates `i₂` using
`i₂ = i₁ + j₁ - j₂` (on sum-diagonals) and `i₂ = i₁ + j₂ - j₁` (on diff-diagonals), reducing
the verification to `O(n³)` triples checked by Lean's kernel `decide` tactic.
-/

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
    ∃ q : Fin n → Fin n, Bijective q ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
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
    ∃ q : Fin 8 → Fin 8, Bijective q ∧ @IsIncremental 8 (@cyclicSquare 8 q h hn) :=
  exists_incremental_of_fin_decide 8 h hn
  -- with
    q8_nat f8_sum f8_diff (by decide)

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
    ∃ q : Fin 9 → Fin 9, Bijective q ∧ @IsIncremental 9 (@cyclicSquare 9 q h hn) :=
  exists_incremental_of_fin_decide 9 h hn
  -- with
    q9_nat f9_sum f9_diff (by decide)

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
    ∃ q : Fin 15 → Fin 15, Bijective q ∧ @IsIncremental 15 (@cyclicSquare 15 q h hn) :=
  exists_incremental_of_fin_decide 15 h hn
  -- with
    q15_nat f15_sum f15_diff (by decide)

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
    ∃ q : Fin 21 → Fin 21, Bijective q ∧ @IsIncremental 21 (@cyclicSquare 21 q h hn) :=
  exists_incremental_of_fin_decide 21 h hn
  -- with
    q21_nat f21_sum f21_diff (by decide)

/-- **Incremental Cyclic Latin Square Conjecture:**
    For every `n > 0` with `n ∉ {2, 3, 4, 6}`, there exists a bijection `q : Fin n → Fin n`
    such that the cyclic Latin square `L(i, j) = (i + q(j)) mod n` is incremental. -/

theorem Conjecture :
  ∀ (n : ℕ)
    (h : n > 0)
    (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6),
  ∃ q : Fin n → Fin n,
        Bijective q
      ∧ @IsIncremental n (@cyclicSquare n q h hn) := by
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

end IncrementalCyclic
