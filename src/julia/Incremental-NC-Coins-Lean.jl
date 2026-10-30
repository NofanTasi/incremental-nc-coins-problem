#!/usr/bin/env julia
# incremental_cyclic_checker.jl
#
# Julia checker mirroring IncrementalCyclic.lean.
# Each function corresponds to a specific Lean definition / lemma / theorem.
#
# Usage:
#   julia Incremental-NC-Coins-Lean.jl # n = 1..40
#   julia Incremental-NC-Coins-Lean.jl 1 60
#   julia Incremental-NC-Coins-Lean.jl 8 8 --board --solutions
#   julia Incremental-NC-Coins-Lean.jl 4 40 --all
#   julia Incremental-NC-Coins-Lean.jl 100 100 fast --board

using Printf

# ============================================================
# §1  Base definitions
#     Lean: val_nat, cyclicSquare, sumDiagOk, diffDiagOk, IsIncremental
# ============================================================

"""
    val_nat(n, p, i, j)   —  Lean: `val_nat n p_nat i j`

Conditional-subtraction form of `(i + p[j+1]) mod n`, valid for `i, p[j+1] < n`.
Equals `L[i+1, j+1]` for `L = cyclicSquare(n, p)` (Lean: `mod_eq_val_nat`).
"""
val_nat(n::Int, p::Vector{Int}, i::Int, j::Int) =
    (s = i + p[j+1]; s < n ? s : s - n)

"""
    cyclicSquare(n, p)   —  Lean: `cyclicSquare n p h hn`

Cyclic Latin square `L[i+1, j+1] = (i + p[j+1]) mod n` (0-indexed entries).
"""
cyclicSquare(n::Int, p::Vector{Int}) =
    [mod(i + p[j+1], n) for i in 0:n-1, j in 0:n-1]

# Diagonal cell generators (0-indexed cells) — the two index ranges
# are exactly the ones Lean's `univ.filter` enumerates.
sum_diag_cells(n::Int, s::Int) =
    [(i, s - i) for i in max(0, s - n + 1):min(n - 1, s)]

diff_diag_cells(n::Int, d::Int) =
    [(i, i - d) for i in max(0, d):min(n - 1, n - 1 + d)]

"""
    sumDiagOk(n, s, k, L)   —  Lean: `sumDiagOk n s k L`

Cells on the sum-diagonal `i + j = s` whose value is at most `k`.
"""
sumDiagOk(n::Int, s::Int, k::Int, L::Matrix{Int}) =
    [c for c in sum_diag_cells(n, s) if L[c[1]+1, c[2]+1] ≤ k]

"""
    diffDiagOk(n, d, k, L)   —  Lean: `diffDiagOk n d k L`

Cells on the diff-diagonal `i - j = d` whose value is at most `k`.
"""
diffDiagOk(n::Int, d::Int, k::Int, L::Matrix{Int}) =
    [c for c in diff_diag_cells(n, d) if L[c[1]+1, c[2]+1] ≤ k]

"""
    is_incremental(n, L)   —  Lean: `IsIncremental n L`

Rows/cols bijective; and for every `k < n`, every sum-diagonal and
diff-diagonal carries at most `k + 1` cells with value ≤ k.
"""
function is_incremental(n::Int, L::Matrix{Int}; verbose::Bool = false)::Bool
    expected = collect(0:n-1)
    all(r -> sort(L[r, :]) == expected, 1:n) ||
        (verbose && println("  row bijection fails"); return false)
    all(c -> sort(L[:, c]) == expected, 1:n) ||
        (verbose && println("  col bijection fails"); return false)
    for k in 0:n-1
        for s in 0:2n-2
            cnt = length(sumDiagOk(n, s, k, L))
            if cnt > k + 1
                verbose && @printf("  sum s=%d k=%d: %d > %d\n", s, k, cnt, k + 1)
                return false
            end
        end
        for d in -(n-1):(n-1)
            cnt = length(diffDiagOk(n, d, k, L))
            if cnt > k + 1
                verbose && @printf("  diff d=%d k=%d: %d > %d\n", d, k, cnt, k + 1)
                return false
            end
        end
    end
    true
end

# ============================================================
# §2  Injective-Majorization Principle
#     Lean: lemma exists_incremental_of_nat
# ============================================================

"""
    check_hypotheses(n, p, f_sum, f_diff)   —  hypotheses of
    `exists_incremental_of_nat`

Checks:
  * `p` is a permutation of `0:n-1`                (hp_lt + hp_inj)
  * `f_sum, f_diff ∈ [0, val_nat]`                 (h_sum_le + h_diff_le,
                                                    ℕ-valued in Lean ⇒ ≥ 0)
  * `f_sum` injective on every sum-diagonal        (h_sum_inj)
  * `f_diff` injective on every diff-diagonal      (h_diff_inj)
"""
function check_hypotheses(n::Int, p::Vector{Int},
                          f_sum::Function, f_diff::Function;
                          verbose::Bool = true)::Bool
    sort(p) == collect(0:n-1) ||
        (verbose && println("  hp_lt / hp_inj FAILS"); return false)
    for i in 0:n-1, j in 0:n-1
        v = val_nat(n, p, i, j)
        fs, fd = f_sum(i, j), f_diff(i, j)
        (fs < 0 || fs > v) &&
            (verbose && @printf("  h_sum_le at (%d,%d): %d ∉ [0,%d]\n", i, j, fs, v); return false)
        (fd < 0 || fd > v) &&
            (verbose && @printf("  h_diff_le at (%d,%d): %d ∉ [0,%d]\n", i, j, fd, v); return false)
    end
    for s in 0:2n-2
        allunique(f_sum(i, j) for (i, j) in sum_diag_cells(n, s)) ||
            (verbose && @printf("  h_sum_inj s=%d\n", s); return false)
    end
    for d in -(n-1):(n-1)
        allunique(f_diff(i, j) for (i, j) in diff_diag_cells(n, d)) ||
            (verbose && @printf("  h_diff_inj d=%d\n", d); return false)
    end
    true
end

"""
    check_pigeonhole(n, L, f_sum, f_diff)   —  diagonal-bound argument in
    `exists_incremental_of_nat`

For each `k < n` and each sum/diff diagonal, the `f`-values of the cells
with `L ≤ k` lie in `[0, k]` and are pairwise distinct — hence at most
`k + 1` such cells (pigeonhole).
"""
function check_pigeonhole(n::Int, L::Matrix{Int},
                          f_sum::Function, f_diff::Function;
                          verbose::Bool = true)::Bool
    for k in 0:n-1
        for s in 0:2n-2
            vals = [f_sum(i, j) for (i, j) in sumDiagOk(n, s, k, L)]
            if !isempty(vals) && (!all(v -> 0 ≤ v ≤ k, vals) || !allunique(vals))
                verbose && @printf("  pig sum s=%d k=%d\n", s, k); return false
            end
        end
        for d in -(n-1):(n-1)
            vals = [f_diff(i, j) for (i, j) in diffDiagOk(n, d, k, L)]
            if !isempty(vals) && (!all(v -> 0 ≤ v ≤ k, vals) || !allunique(vals))
                verbose && @printf("  pig diff d=%d k=%d\n", d, k); return false
            end
        end
    end
    true
end

# ============================================================
# §3  Family 1 — n ≡ 1, 5 (mod 6)
#     Lean: p1_nat, solve_family1
# ============================================================

"""
    p1_nat(n, j)   —  Lean: `p1_nat n j`

`p1(j) = (-2j) mod n`, written as three linear branches.
"""
p1_nat(n::Int, j::Int) =
    j == 0   ? 0       :
    2j < n   ? n - 2j  :
               2n - 2j

"""
    family1(n)   —  Lean: `solve_family1`

`gcd(6, n) = 1` ⇒ no diagonal collisions ⇒ `f_sum = f_diff = val_nat`.
"""
function family1(n::Int)
    p = [p1_nat(n, j) for j in 0:n-1]
    p, ((i, j) -> val_nat(n, p, i, j)), ((i, j) -> val_nat(n, p, i, j)),
    "Family 1  (n≡1,5 mod 6)"
end

# ============================================================
# §4  Family 2 — n ≡ 2, 4 (mod 6), n ≥ 10
#     Lean: p2_nat, f2_sum, f2_diff, solve_family2
# ============================================================

"""
    p2_nat(n, j)   —  Lean: `p2_nat n j`

Two-block permutation: step `+2` inside each half of `n/2`, with a `+3`
parity switch at `j = n/2`.
"""
p2_nat(n::Int, j::Int) =
    let m = n ÷ 2
        if j < m
            v = 2j + m + 1
            v < n ? v : v - n
        else
            v = 2(j - m) + m + 4
            v < n ? v : v - n
        end
    end

"""
    family2(n)   —  Lean: `solve_family2`

`f2_sum` shifts the 3×3 top-right corner; `f2_diff` shifts cell `(n-1, n-1)`.
"""
function family2(n::Int)
    p = [p2_nat(n, j) for j in 0:n-1]
    f_sum  = (i, j) -> (i < 3     && j ≥ n - 3) ? j - (n - 3) : val_nat(n, p, i, j)
    f_diff = (i, j) -> (i == n-1  && j == n-1 ) ? 1           : val_nat(n, p, i, j)
    p, f_sum, f_diff, "Family 2  (n≡2,4 mod 6, n≥10)"
end

# ============================================================
# §5  Family 3 — n ≡ 3 (mod 6), n ≥ 27
#     Lean: p3_nat, f3_sum, f3_diff, solve_family3
# ============================================================

"""
    p3_nat(n, j)   —  Lean: `p3_nat n j`

Three-block permutation: step `+3` inside each block of length `k = n/3`,
with `+4` jumps between blocks.
"""
p3_nat(n::Int, j::Int) =
    let k = n ÷ 3
        j < k    ? (v = 3j          + 2k;     v < n ? v : v - n) :
        j < 2k   ? (v = 3(j - k)    + 2k + 4; v < n ? v : v - n) :
                   (v = 3(j - 2k)   + 2k + 8; v < n ? v : v - n)
    end

"""
    family3(n)   —  Lean: `solve_family3`

`f3_sum` shifts the 4×4 top-right corner; `f3_diff` shifts the 2×2
bottom-right corner.
"""
function family3(n::Int)
    p = [p3_nat(n, j) for j in 0:n-1]
    k = n ÷ 3
    f_sum  = (i, j) -> let v = val_nat(n, p, i, j)
        i < 4 && (j == n-4 || j == n-3) ? v - k  :
        i < 4 && (j == n-2 || j == n-1) ? v - 2k :
                                          v
    end
    f_diff = (i, j) -> let v = val_nat(n, p, i, j)
        i ≥ n-2 && j == n-2 ? v - 2k :
        i ≥ n-2 && j == n-1 ? v - k  :
                              v
    end
    p, f_sum, f_diff, "Family 3  (n≡3 mod 6, n≥27)"
end

# ============================================================
# §6  Family 4 — n ≡ 0 (mod 6), n ≥ 12
#     Lean: p4_nat, f4_sum, f4_diff, solve_family4
# ============================================================

"""
    p4_nat(n, j)   —  Lean: `p4_nat n j`

Five-piece permutation: boundary pins `{0, m-2, n-1}` + two main blocks
(even residues / odd residues) with `m = n/2`.
"""
p4_nat(n::Int, j::Int) =
    let m = n ÷ 2
        j == 0    ? n - 2                :
        j < m - 2 ? 2j + 2               :
        j == m - 2 ? 0                   :
        j < n - 1 ? 2(j - (m - 1)) + 1   :
                    2
    end

"""
    family4(n)   —  Lean: `solve_family4`

`f4_sum` shifts three seam columns; `f4_diff` shifts wrapped portions of
each block into the vacant mod-3 residue class.
"""
function family4(n::Int)
    p = [p4_nat(n, j) for j in 0:n-1]
    m, k = n ÷ 2, n ÷ 3
    f_sum = (i, j) -> let v = val_nat(n, p, i, j)
        j == m - 1 && i < n - 1 ? v - 1       :
        j == n - 5 && i + j < n ? v - (m - 2) :
        j == n - 1 && i < 2     ? v - 1       :
                                  v
    end
    f_diff = (i, j) -> let v = val_nat(n, p, i, j)
        1 + k ≤ j ≤ m - 3     && i ≥ k          ? v - 1 :
        j == m - 1 + k && k ≤ i < 2k            ? v - 1 :
        j == m - 1 + k && i ≥ 2k && n == 12     ? v - 4 :
        j == m - 1 + k && i ≥ 2k && n != 12     ? v - 5 :
        m + k ≤ j ≤ n - 2     && i ≥ k          ? v - 2 :
                                                  v
    end
    p, f_sum, f_diff, "Family 4  (n≡0 mod 6, n≥12)"
end

# ============================================================
# §7  Small exceptional cases n = 8, 9, 15, 21
#     Lean: p{8,9,15,21}_nat, f*_{sum,diff}, solve_{8,9,15,21}
# ============================================================

const P8  = [0, 4, 1, 3, 6, 2, 7, 5]
const P9  = [0, 6, 3, 1, 8, 5, 2, 4, 7]
const P15 = [0, 3, 6, 9, 12, 8, 5, 2, 13, 1, 4, 7, 10, 14, 11]
const P21 = [0, 18, 15, 12, 9, 6, 3, 7, 4, 1, 14, 17, 10, 16, 2, 5, 11, 8, 20, 13, 19]

function small_case(n::Int)
    if n == 8
        f_sum  = (i, j) -> (j == 3 && i < 4) ? i + 1 :
                           (j == 3 && i == 4) ? 3    :
                           val_nat(8, P8, i, j)
        f_diff = (i, j) -> (j == 6 && (i == 5 || i == 6)) ? i - 5 :
                           (j == 6 && i == 7)             ? 5     :
                           val_nat(8, P8, i, j)
        P8, f_sum, f_diff, "Small case n=8"
    elseif n == 9
        f_sum  = (i, j) -> (j == 5 && i < 3)              ? i + 4  :
                           (j == 5 && i == 3)             ? 2      :
                           (j == 6 && i < 2)              ? i      :
                           (j == 6 && (i == 2 || i == 3)) ? 2i - 3 :
                           val_nat(9, P9, i, j)
        f_diff = (i, j) -> val_nat(9, P9, i, j)
        P9, f_sum, f_diff, "Small case n=9"
    elseif n == 15
        f_sum  = (i, j) -> val_nat(15, P15, i, j)
        f_diff = (i, j) -> (j == 13 && i == 10)                         ? 5     :
                           (j == 13 && 11 ≤ i ≤ 14)                     ? i - 8 :
                           (j == 14 && (i == 5 || i == 6))              ? i - 5 :
                           (j == 14 && 7 ≤ i ≤ 10)                      ? i - 6 :
                           (j == 14 && (i == 11 || i == 12 || i == 14)) ? 2     :
                           (j == 14 && i == 13)                         ? 1     :
                           val_nat(15, P15, i, j)
        P15, f_sum, f_diff, "Small case n=15"
    elseif n == 21
        f_sum = (i, j) -> let v = val_nat(21, P21, i, j)
            j == 7  && i ≤ 12                                    ? i + 6 :
            j == 7  && i == 13                                   ? 13    :
            j == 8  && i ≤ 7                                     ? i + 3 :
            j == 8  && 8 ≤ i ≤ 10                                ? i + 2 :
            j == 8  && (i == 11 || i == 13)                      ? i + 1 :
            j == 8  && i == 12                                   ? 9     :
            j == 9  && i ≤ 7                                     ? i     :
            j == 9  && (i == 8 || i == 9 || i == 10 || i == 12 || i == 13) ? i - 2 :
            j == 9  && i == 11                                   ? 7     :
            j == 14 && i ≤ 5                                     ? i + 1 :
            j == 14 && i == 6                                    ? 6     :
            j == 14 && 7 ≤ i ≤ 9                                 ? i + 1 :
                                                                   v
        end
        f_diff = (i, j) -> let v = val_nat(21, P21, i, j)
            j == 18 && 16 ≤ i ≤ 20 ? i - 13 :
            j == 19 && 14 ≤ i ≤ 16 ? i - 14 :
            j == 19 && 17 ≤ i ≤ 20 ? i - 17 :
                                     v
        end
        P21, f_sum, f_diff, "Small case n=21"
    else
        error("small_case: n=$n not in {8,9,15,21}")
    end
end

# ============================================================
# §8  Non-cyclic boards L4, L6
#     (not covered by Lean: the Conjecture excludes n = 4, 6)
# ============================================================

const L4 = [3 2 0 1;
            0 1 2 3;
            2 3 1 0;
            1 0 3 2]

const L6 = [4 5 2 3 0 1;
            5 3 0 2 1 4;
            0 1 3 5 4 2;
            2 4 5 1 3 0;
            1 2 4 0 5 3;
            3 0 1 4 2 5]

# ============================================================
# §9  Thresholding
#     Lean: thresholdBoard, n_c_of_isIncremental
# ============================================================

"""
    thresholdBoard(n, c, L)   —  Lean: `thresholdBoard`

Cells `(i, j)` with `L[i+1, j+1] < c`, i.e. `S_c` of size `n*c`.
"""
thresholdBoard(n::Int, c::Int, L::Matrix{Int}) =
    [(i, j) for i in 0:n-1, j in 0:n-1 if L[i+1, j+1] < c]

"""
    check_nc_solution(n, c, L)   —  Lean: `n_c_of_isIncremental`

Verifies `S_c = {L < c}` is an (n, c)-coins solution: `n*c` cells and at
most `c` per row / column / sum-diagonal / diff-diagonal.
"""
function check_nc_solution(n::Int, c::Int, L::Matrix{Int}; verbose::Bool = true)::Bool
    S = thresholdBoard(n, c, L)
    length(S) == n * c ||
        (verbose && @printf("  |S_%d| = %d ≠ %d\n", c, length(S), n * c); return false)
    rows = zeros(Int, n); cols = zeros(Int, n)
    for (i, j) in S
        rows[i+1] += 1; cols[j+1] += 1
    end
    all(r -> rows[r] ≤ c, 1:n) ||
        (verbose && println("  row count exceeds c"); return false)
    all(k -> cols[k] ≤ c, 1:n) ||
        (verbose && println("  col count exceeds c"); return false)
    for s in 0:2n-2
        cnt = count(cell -> cell[1] + cell[2] == s, S)
        cnt > c && (verbose && @printf("  sum s=%d: %d > %d\n", s, cnt, c); return false)
    end
    for d in -(n-1):(n-1)
        cnt = count(cell -> cell[1] - cell[2] == d, S)
        cnt > c && (verbose && @printf("  diff d=%d: %d > %d\n", d, cnt, c); return false)
    end
    true
end

# ============================================================
# §10  Printing
# ============================================================

function print_board(n::Int, L::Matrix{Int})
    w = ndigits(n - 1)
    println("  Incremental board L (0-based), $(n)×$(n):")
    foreach(i -> println("    ", join(lpad.(L[i, :], w), " ")), 1:n)
    println()
end

function print_threshold(n::Int, c::Int, L::Matrix{Int})
    S = Set(thresholdBoard(n, c, L))
    println("  S_$c = {L < $c}   (|S_$c| = $(length(S)) = $n×$c):")
    for i in 0:n-1
        println("    ", join([(i, j) in S ? "X" : "." for j in 0:n-1], " "))
    end
    println()
end

# ============================================================
# §11  Driver — mirrors theorem Conjecture
# ============================================================

function solve(n::Int)
    n < 1            && return (status = :error, msg = "n must be ≥ 1")
    n in (2, 3)      && return (status = :no_solution,
                                msg = "no (n,1)-queens solution exists")
    n == 1           && return (status = :ok, n = 1, p = [0],
                                L = cyclicSquare(1, [0]),
                                tag = "Trivial n=1",
                                f_sum = nothing, f_diff = nothing)
    n == 4           && return (status = :ok, n = 4, p = nothing, L = L4,
                                tag = "Non-cyclic L4",
                                f_sum = nothing, f_diff = nothing)
    n == 6           && return (status = :ok, n = 6, p = nothing, L = L6,
                                tag = "Non-cyclic L6",
                                f_sum = nothing, f_diff = nothing)

    (p, f_sum, f_diff, tag) =
        n in (8, 9, 15, 21)       ? small_case(n) :
        n % 6 in (1, 5)           ? family1(n)    :
        n % 6 in (2, 4) && n ≥ 10 ? family2(n)    :
        n % 6 == 3      && n ≥ 27 ? family3(n)    :
        n % 6 == 0      && n ≥ 12 ? family4(n)    :
        error("no family covers n=$n")

    (status = :ok, n = n, p = p, L = cyclicSquare(n, p),
     tag = tag, f_sum = f_sum, f_diff = f_diff)
end

# ============================================================
# §12  CLI
# ============================================================

function usage()
    println("usage: julia Incremental-NC-Coins-Lean.jl [nmin] [nmax] [options]")
    println("options:")
    println("  fast            skip pigeonhole + thresholding checks")
    println("  --board         print incremental board L")
    println("  --solutions     print S_c = {L < c} for each c")
    println("  --all           --board --solutions")
    println("  --no-threshold  skip S_c verification even without fast")
    println("  --help, -h      show this message")
end

function main(args)
    nmin, nmax = 1, 40
    fast = false; do_board = false; do_sol = false; do_thresh = true
    positional = String[]
    for a in args
        a == "fast"            && (fast = true)
        a == "--board"         && (do_board = true)
        a == "--solutions"     && (do_sol = true)
        a == "--all"           && (do_board = true; do_sol = true)
        a == "--no-threshold"  && (do_thresh = false)
        a in ("--help", "-h")  && (usage(); return)
        startswith(a, "-")     || push!(positional, a)
    end
    length(positional) ≥ 1 && (nmin = parse(Int, positional[1]))
    length(positional) ≥ 2 && (nmax = parse(Int, positional[2]))

    println("="^70)
    println("Incremental Cyclic Latin Square Checker")
    println("Mirror of IncrementalCyclic.lean")
    println("="^70); println()

    all_ok = true; verified = 0; skipped = 0
    for n in nmin:nmax
        result = solve(n)
        if result.status == :no_solution
            @printf("n=%3d  [exception]  %s\n", n, result.msg); skipped += 1; continue
        elseif result.status == :error
            @printf("n=%3d  [error]  %s\n", n, result.msg); all_ok = false; continue
        end

        L = result.L
        inc = is_incremental(n, L)
        hyp = result.f_sum === nothing ? nothing :
              check_hypotheses(n, result.p, result.f_sum, result.f_diff; verbose = false)
        pig = (result.f_sum === nothing || fast) ? nothing :
              check_pigeonhole(n, L, result.f_sum, result.f_diff; verbose = false)
        thr = (!fast && do_thresh) ?
              all(check_nc_solution(n, c, L; verbose = false) for c in 0:n) :
              nothing

        parts = String[]
        push!(parts, inc ? "inc ✓" : "inc ✗")
        hyp !== nothing && push!(parts, hyp ? "hyp ✓" : "hyp ✗")
        pig !== nothing && push!(parts, pig ? "pig ✓" : "pig ✗")
        thr !== nothing && push!(parts, thr ? "thr ✓" : "thr ✗")

        ok = inc && (hyp === nothing || hyp) && (pig === nothing || pig) &&
             (thr === nothing || thr)
        ok || (all_ok = false)
        ok && (verified += 1)

        @printf("n=%3d  [%s]  %s\n", n, rpad(result.tag, 30), join(parts, "  "))
        do_board && print_board(n, L)
        if do_sol
            foreach(c -> print_threshold(n, c, L), 0:n)
        end
    end

    println(); println("="^70)
    @printf("%d verified, %d skipped (2,3), status: %s\n",
            verified, skipped,
            all_ok ? "ALL CHECKS PASSED" : "SOME CHECKS FAILED")
    println("="^70)
end

main(ARGS)
