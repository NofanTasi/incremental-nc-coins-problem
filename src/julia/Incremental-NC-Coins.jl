# ============================================================================
# Incremental (n,c)-Coins Generator, Verifier, and Display Engine
#  twin Based
# on Luc Duponcheel's Lean formalization
#  and
# on some Marc Duponcheel's ideas and reports
# ============================================================================

# ============================================================================
# 1. Utilities
# ============================================================================
"""
 * cyclic(n,p)
Constructs the 0:(n-1) valued cyclic Latin square L[i,j] = (i + p[j]) mod n.
"""
cyclic(n,p) = [mod(i+p[j],n) for i in 0:(n-1), j in 1:n]

# ============================================================================
# 2. Families (compressed somewhat compact formulas extracted from Lean)
# ============================================================================
"""
 * F_f(n,j)
Formula for permutation p to be used by Family f
"""
# Family 1: n = 1 or 5 (mod 6) (n >= 1)
F_1(n,j) = j == 0 ? 0 : 2j < n ? n - 2j : 2n - 2j

# Family 2: n = 2 or 4 (mod 6) (n >= 10)
F_2(n,j) = (d = div(n,2); r = j < d ? 2j + d + 1 : 2(j - d) + d + 4; r < n ? r : r - n)

# Family 3: n = 0 (mod 6) (n >= 12)
F_3(n,j) = (d = div(n,2); j == 0 ? n - 2 : j < d - 2 ? 2j + 2 : j == d - 2 ? 0 : j < n - 1 ? 2(j - d + 1) + 1 : 2)

# Family 4: n = 3 (mod 6) (n >= 27)
F_4(n,j) = (d = div(n,3); r = j < d ? 3j + 2d : j < 2d ? 3(j - d) + 2d + 4 : 3(j - 2d) + 2d + 8; r < n ? r : r - n)

# some finite small Permutations (0:(n-1) valued) below minimal values supported per family
const Qs = Dict(
    8  => [0,4,1,3,6,2,7,5], # f2: 8 < 10
    9  => [0,6,3,1,8,5,2,4,7], # f3: 9 < 27
    15 => [0,3,6,9,12,8,5,2,13,1,4,7,10,14,11], # f3: 15 < 27
    21 => [0,18,15,12,9,6,3,7,4,1,14,17,10,16,2,5,11,8,20,13,19] # f3: 21 < 27
)

# get F_f where 1 <= f <= 4 providing p for Family f
function get_f_for_p(n)
    if haskey(Qs,n)
        return (n,j) -> Qs[n][j+1]
    end

    # minimal values per family
    (m_2,m_3,m_4) = (10,12,27)

    r = mod(n,6)
    if r == 1 || r == 5
        return F_1
    elseif r == 2 || r == 4
        n >= m_2 || error("Family 2 requires n >= $m_2 (n = $n)")
        return F_2
    elseif r == 0
        n >= m_3 || error("Family 3 requires n >= $m_3 (n = $n)")
        return F_3
    elseif r == 3
        n >= m_4 || error("Family 4 requires n >= $m_4 (n = $n)")
        return F_4
    else
        error("Unsupported Dimension n = $n")
    end
end

# ============================================================================
# 3. board Verification
# ============================================================================
"""
 * correct(L,n)
Verifies that L is a 0:(n-1)-valued Latin square (bijective rows and columns)
and that, for every threshold c (0 <= c <= n), every sum-diagonal and
dif-diagonal contains at most c cells with value < c.
"""
function correct(L,n)
    # 1. Check Row and Col Bijectivity
    #    L is 0:(n-1)-valued; isperm expects 1:n, so shift by 1 first.
    for r in 1:n
        if !isperm(L[r,:] .+ 1)
            return false,"Row $r is not a Permutation"
        end
    end
    for c in 1:n
        if !isperm(L[:,c] .+ 1)
            return false,"Col $c is not a Permutation"
        end
    end

    # 2. Check Diagonals for every threshold c
    for c in 0:n
        # Check all sum-diagonals (sum s from 0 to 2n-2)
        for s in 0:(2n-2)
            cnt = count(i->L[i+1,s-i+1] < c, max(0,s-n+1):min(n-1,s))
            if cnt > c
                return false,
                "Sum-diagonal $s count $cnt > $c (threshold c=$c)"
            end
        end

        # Check all dif-diagonals (dif d from -(n-1) to n-1)
        for d in -(n-1):(n-1)
            cnt = count(i->L[i+1,i-d+1] < c, max(0,d):min(n-1,n-1+d))
            if cnt > c
                return false,
                "Dif-diagonal $d count $cnt > $c (threshold c=$c)"
            end
        end
    end

    return true,"verification success!"
end

# ============================================================================
# 4. Solver & Display
# ============================================================================
"""
 * solve(range;print_p,print_L,print_I,verify,benchmark)
Generates, optionally benchmarks, verifies, displays any range of n and its nc's.
"""
function solve(range;
               print_p=true, # print permutation p
               print_L=true, # print latin square L solution
               print_I=false, # print incremental boards
               verify=true, # verify solution
               benchmark=false # benchmark execution
               )

    if benchmark
        (e,t) = (2,time())
    end

    for n in range
        # pad length
        l = Int(floor(log(10,n)))+2

        if !benchmark
            println("Incremental board for n = $n")
        end

        if n < 4
            println("skipping Dimension n = $n < 4")
            continue
        elseif n == 4
            # an Explicit non-cyclic L4 (0:(n-1)-valued)
            L = [
                2 0 1 3;
                1 3 2 0;
                0 2 3 1;
                3 1 0 2
            ]
            p = missing
        elseif n == 6
            # an Explicit non-cyclic L6 (0:(n-1)-valued)
            L = [
                1 0 2 3 5 4;
                3 1 4 0 2 5;
                4 3 5 2 1 0;
                0 2 1 5 4 3;
                2 5 0 4 3 1;
                5 4 3 1 0 2
            ]
            p = missing
        else
            p = [get_f_for_p(n)(n,j) for j in 0:(n-1)]
            L = cyclic(n,p)
        end

        if verify
            ok,msg = correct(L,n)
            v = ok ? "OK!: SUCCESS" : "KO?: FAILURE"
            println("$v -> $msg")
        end

        if print_p
            println("column Permutation (0:(n-1) valued):")
            print("p = ")
            println(p)
        end

        if print_L
            println("Incremental Latin Square (0:(n-1) valued):")
            for r in eachrow(L)
                println(" ", join(lpad.(r,l)))
            end
        end

        if print_I
            println("(n,c) Solutions (0:1 valued):")
            for c in 0:n
                println("Increment c = $c:")
                for r in eachrow(L)
                    println(" ", join(lpad.(Int.(r.<c),2),""))
                end
            end
        end

        if benchmark
            if (n == 2^e)
                s = (time() - t) / n
                println("n = $n, t~/n = $s")
                e += 1
            end
        else
            println()
        end
    end
end

# example invocation: 8x8 board and it's (8,c)-coins solutions
# r = collect(8:8)
# solve(r,print_p=true,print_L=true,print_I=true,verify=false)
# exit(0)

# example invocation: show everything and verify up to 32
r = collect(4:32)
solve(r,print_p=true,print_L=true,print_I=true,verify=true)
exit(0)

# example invocation: show nothing and do not verify but benchmark up to 2^12
# r = collect(4:2^12)
# solve(r,print_p=false,print_L=false,print_I=false,verify=false,benchmark=true)
# exit(0)
