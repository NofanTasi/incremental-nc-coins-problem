# ============================================================================
# Incremental (n,c)-Coins Generator, Verifier, and Display Engine
# Calculate and print optional 2D Discrete Fourier Transform
#  twin Based
# on Luc Duponcheel's Lean formalization
#  and
# on some Marc Duponcheel's ideas and reports
# ============================================================================

using FFTW

# ============================================================================
# 1. Utilities
# ============================================================================
"""
 * cyclic(n,q)
Constructs the 1-indexed cyclic Latin square L[i,j] = 1 + ((i + q[j]) mod n).
"""
cyclic(n,q) = [mod(i+q[j],n) + 1 for i in 0:(n-1), j in 1:n]

# ============================================================================
# 2. Families (compressed somewhat compact formulas extracted from Lean)
# ============================================================================

# Family 1: n = 1 or 5 (mod 6) (n >= 1)
F_1(n,j) = j == 0 ? 0 : 2j < n ? n - 2j : 2n - 2j

# Family 2: n = 2 or 4 (mod 6) (n >= 10)
F_2(n,j) = (d = div(n,2); r = j < d ? 2j + d + 1 : 2(j - d) + d + 4; r < n ? r : r - n)

# Family 3: n = 0 (mod 6) (n >= 12)
F_3(n,j) = (d = div(n,2); j == 0 ? n - 2 : j < d - 2 ? 2j + 2 : j == d - 2 ? 0 : j < n - 1 ? 2(j - d + 1) + 1 : 2)

# Family 4: n = 3 (mod 6) (n >= 27)
F_4(n,j) = (d = div(n,3); r = j < d ? 3j + 2d : j < 2d ? 3(j - d) + 2d + 4 : 3(j - 2d) + 2d + 8; r < n ? r : r - n)

# some finite small Permutations (0-indexed) below minimal values supported per family
const Qs = Dict(
    8  => [0,4,1,3,6,2,7,5], # f2: 8 < 10
    9  => [0,6,3,1,8,5,2,4,7], # f3: 9 < 27
    15 => [0,3,6,9,12,8,5,2,13,1,4,7,10,14,11], # f3: 15 < 27
    21 => [0,18,15,12,9,6,3,7,4,1,14,17,10,16,2,5,11,8,20,13,19] # f3: 21 < 27
)

# get F_f where 1 <= f <= 4 providing q for Family f
function get_f_q(n)
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
Verifies that L is a Latin square (bijective rows and columns) and that 
for every threshold c (1 <= c <= n), every sum-diagonal and dif-diagonal 
contains at most c cells with value <= c.
"""
function correct(L,n)
    # 1. Check Row and Col Bijectivity
    for r in 1:n
        if !isperm(L[r,:])
            return false,"Row $r is not a Permutation"
        end
    end
    for c in 1:n
        if !isperm(L[:,c])
            return false,"Col $c is not a Permutation"
        end
    end

    # 2. Check Diagonal Capacities for every threshold c
    for c in 1:n
        # Check all sum-diagonals (0-indexed sum s from 0 to 2n-2)
        for s in 0:(2n-2)
            cnt = count(i->L[i+1,s-i+1] <= c, max(0,s-n+1):min(n-1,s))
            if cnt > c
                return false,
                "Sum-diagonal $s count $cnt > $c"
            end
        end

        # Check all dif-diagonals (0-indexed dif d from -(n-1) to n-1)
        for d in -(n-1):(n-1)
            cnt = count(i->L[i+1,i-d+1] <= c, max(0,d):min(n-1,n-1+d))
            if cnt > c
                return false,
                "Dif-diagonal $d count $cnt > $c"
            end
        end
    end

    return true,"verification success!"
end

# ============================================================================
# 4. Take and Show 2D Discrete Fourier Transform of M
# ============================================================================
function show_dft(M, n)
    vs = round.(log.(1 .+ abs.(fft(M))[1:n,1:n]), digits=1)
    foreach(println, [join(lpad.(r, 5)) for r in eachrow(vs)])
end

# ============================================================================
# 5. Solver & Display
# ============================================================================
"""
 * solve(range;print_q,print_L,print_I,print_D,verify,benchmark)
Generates, optionally benchmarks, verifies, displays any range of n and its c's.
"""
function solve(range;print_q=true,print_L=true,print_I=false,print_D=false,verify=true,benchmark=false)
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
            println("KO? Dimension n = $n < 4")
            continue
        elseif n == 4
            # an Explicit non-cyclic L4
            L = [
                3 1 2 4;
                2 4 3 1;
                1 3 4 2;
                4 2 1 3
            ]
            q = missing
        elseif n == 6
            # an Explicit non-cyclic L6
            L = [
                2 1 3 4 6 5;
                4 2 5 1 3 6;
                5 4 6 3 2 1;
                1 3 2 6 5 4;
                3 6 1 5 4 2;
                6 5 4 2 1 3
            ]
            q = missing
        else
            q = [get_f_q(n)(n,j) for j in 0:(n-1)]
            L = cyclic(n,q)
            q = q .+ 1
        end

        if verify
            ok,msg = correct(L,n)
            v = ok ? "OK!: SUCCESS" : "KO?: FAILURE"
            println("$v -> $msg")
        end

        if print_q
            println("column Permutation (1-indexed):")
            print("q = ")
            println(q)
        end

        if print_L
            println("Incremental Latin Square:")
            for r in eachrow(L)
                println(" ", join(lpad.(r,l)))
            end
   	    if print_D
                println("Incremental Latin Square DFT:")
                show_dft(L,n)
            end
        end

        if print_I
            println("(n,c) Solutions ((0|1) valued):")
            for c in 1:n
                println("Increment c = $c:")
                for r in eachrow(L)
                    println(" ", join(lpad.(Int.(r.<=c),2),""))
                end
            end
            if print_D
                for c in 1:n
                    println("Increment c = $c DFT:")
                    I::Matrix{Int} = zeros(n,n)
                    I .= Int.(L .<= c)
                    show_dft(I,n)
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

function print_coins_solution(n, c)
    if n < 4
        println("KO? Dimension n = $n < 4")
        return
    elseif c > n
        println("Invalid parameter c = $c: must satisfy c ≤ n = $n.")
        return
    end
    L = n == 4 ? [3 1 2 4; 2 4 3 1; 1 3 4 2; 4 2 1 3] :
        n == 6 ? [2 1 3 4 6 5; 4 2 5 1 3 6; 5 4 6 3 2 1; 1 3 2 6 5 4; 3 6 1 5 4 2; 6 5 4 2 1 3] :
        cyclic(n, [get_f_q(n)(n,j) for j in 0:(n-1)])
    println("=== ($n, $c)-Coins Solution ($n × $n board, $(n*c) coins) ===")
    for r in eachrow(L)
        println(join([x <= c ? "C " : ". " for x in r]))
    end
end

# ============================================================================
# uncomment one of the two triples of lines below for interpretation
# ============================================================================

# r = collect(4:32)
# solve(r,print_q=true,print_L=true,print_I=true,print_D=true,verify=true)
# exit(0)

# or

# r = collect(4:1024)
# solve(r,print_q=false,print_L=false,print_I=false,print_D=false,verify=false,benchmark=true)
# exit(0)

# ============================================================================
# uncomment the lines below for compilation
# ============================================================================

function main() 

    # TODO : why is this extra ARGS[2] != "-v" needed ?
    if (ARGS[1] == "-incremental") && ARGS[2] != "-v" && (length(ARGS) == 2)
        n = parse(Int, ARGS[2])
        solve(n:n, print_q=true, print_L=true, print_I=false, verify=false)
    elseif ARGS[1] == "-coins" && length(ARGS) == 3
        n = parse(Int, ARGS[2])
        c = parse(Int, ARGS[3])
        print_coins_solution(n, c) 
    elseif ARGS[1] == "-incremental" && ARGS[2] == "-v" && length(ARGS) == 3
        n = parse(Int, ARGS[3])        
        solve(n:n, print_q=true, print_L=true, print_I=false, verify=true)  

    # elseif ARGS[1] == "--batch"
    #     r = collect(4:32)
    #     solve(r, print_q=true, print_L=true, print_I=true, verify=true)
    # elseif length(ARGS) == 1 && tryparse(Int, ARGS[1]) !== nothing
    #     n = parse(Int, ARGS[1])
    #     solve(n:n, print_q=true, print_L=true, print_I=false, verify=false)

    else
        # TODO : why is foo printed using ./run.sh -increment -v 5 ?
        println("foo")
    end
end

main()
