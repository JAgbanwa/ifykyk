# The posed equation is `x³ + y³ + z³ = 114` in disguise

## TL;DR

The equation

```
y² = (A·s + B·t + C)² + N(s)/(B·t + β)
```

with your 60- and 180-digit constants, restricted to `s = a/b`, `t = c/d` with
`b | 3β` and `d | 2β`, is **exactly equivalent** to finding integer solutions of

```
x³ + y³ + z³ = 114
```

114 is the smallest unsolved case of the sum-of-three-cubes problem. Booker and
Sutherland ran precisely this search on Charity Engine and found nothing with
`min(|x|,|y|,|z|) ≤ 10¹⁹`. So the answer set for your `(s,t)` question is, as of
today, **empty** — and populating it means beating the current world record on a
known-hard open problem, not running a clever script.

Everything below is verified by the scripts in this directory, not asserted.

---

## The reduction

Let

```
β  = 176959370426063526189820447723837571181114689072145824174813     (prime)
ν  = 74604001735631008979979919114739993010174529587863668273099
```

Then the constants are not arbitrary:

| relation | |
|---|---|
| `B = 2β`, `A = 18β` | |
| `C − β = 18ν` | |
| `n₃ = 972β³ = 3A²β` | |
| your bound on `den(s)`, `530878…524439` | `= 3β` |
| your bound on `den(t)`, `353918…349626` | `= 2β` |

**Identity 1** — the cubic numerator is an expanded cube:

```
N(s) = ( (A·s + C − β)³ − 114 ) / 6
```

(This is why depressing the cubic gives `p = 0` and `q = −19/n₃`: it has a triple
root over ℂ up to the constant −19.)

**Identity 2** — with `P = A·s + B·t + C` and `D = B·t + β`:

```
(P+D)³ + (−(D+y))³ + (y−D)³ − 114  =  6·D·( P² + N(s)/D − y² )
```

The right side vanishes **iff** `y² = P² + N(s)/D`. Hence

```
y² = P² + N(s)/D     ⟺     p³ + q³ + r³ = 114
```

with `p = P+D`, `q = −(D+y)`, `r = y−D`.

**Clean coordinates.** Put `X = 3βs + 3ν` and `U = β(2t+1)`. Then `P = 6X + U`,
`N/D = (36X³ − 19)/U`, and the whole problem is

```
y² = (6X + U)² + (36X³ − 19)/U ,   X, U ∈ ℤ, U ≠ 0
```

**Your denominator constraints are not a constraint.** `b | 3β` ⟺ `X ∈ ℤ`, and
`d | 2β` ⟺ `U ∈ ℤ`. Since β is prime, the only available denominators are
`b ∈ {1, 3, β, 3β}` and `d ∈ {1, 2, β, 2β}` — that is the entire content of the
divisibility conditions.

---

## The dictionary

Given a solution of `x³+y³+z³ = 114`: exactly one coordinate is even (all-even
is impossible, since `8 ∤ 114`). Call it `p`; the two odd ones are `q, r`. Then
`p+q+r ≡ 0 (mod 6)` automatically, and

```
X = (p+q+r)/6        s = (X − 3ν)/(3β)
U = −(q+r)/2         t = (U − β)/(2β)
y = (r−q)/2
```

Swapping `q ↔ r` only flips the sign of `y`, giving the same `(s,t)`.

The side conditions in your problem statement map to exactly the two degenerate
families of the cubic problem:

| your condition | cube-side meaning |
|---|---|
| `B·t + β ≠ 0` (denominator) | `U ≠ 0` ⟺ `q = −r` ⟺ the `x = −y` family (needs `z³ = 114`; impossible) |
| `y` nonzero | `q ≠ r` ⟺ the `y = z` family, i.e. the Thue equation `x³ + 2y³ = 114` |
| `s`, `t` non-integer | `X ≢ 3ν (mod 3β)`, `U ≢ β (mod 2β)` — checked in code; will pass for any real solution |
| `(a,b) ≠ (c,d)` | `2(X − 3ν) ≠ 3(U − β)` — likewise |

So: **the non-integer `(s,t)` you are asking for are in bijection with the
solutions of `114 = x³+y³+z³` having three distinct coordinates.**

---

## Status of the target

- 114 is the smallest `k` with `k ≢ ±4 (mod 9)` for which no representation is known.
  Remaining open `k < 1000`: 114, 390, 627, 633, 732, 921, 975.
- Booker (2019) ruled out `min(|x|,|y|,|z|) ≤ 10¹⁶`; Booker–Sutherland's Charity
  Engine run (2019) used `zmax = 10¹⁷`, and Charity Engine's follow-up through
  2020 used `zmax = 10¹⁹`, `dmax = zmax/54`. 114 survived all of it.
- Heath-Brown's conjectured density gives `ρ_sol(114) = 0.058459`, i.e. ~2 expected
  solutions with `max ≤ 10¹⁵` — and zero found. 114 is already an outlier, so the
  first solution may be badly skewed (compare `k = 3`, where `|z| ≈ 4.7×10¹⁷`
  but `|x|,|y| ≈ 5.7×10²⁰`).

---

## Files

| file | what it does |
|---|---|
| `reduction.py` | proves the reduction: constant structure, both symbolic identities, 200 random exact numeric checks (needs sympy) |
| `st_cubes.py` | the dictionary, both directions, plus a full validity checker for the original problem; `scan` converts searcher output into `(s,t,y)` |
| `search_cubes.c` | the actual search: Booker's divisor method for `x³+y³+z³=k`, `k ≡ ±3 (mod 9)` |
| `make_wu.py` | work-unit planner (geometric split) and result aggregator |
| `degenerate.py` | the three families the divisor search does not cover, enumerated to completion |

## Build and run

```sh
gcc -O3 -march=native -o search_cubes search_cubes.c -lm

python3 reduction.py                 # verify the reduction
python3 st_cubes.py selftest         # verify the dictionary
python3 degenerate.py                # clear the degenerate families

# validation: rediscover known solutions from a cold sweep
./search_cubes -k 39 -d0 1 -d1 30000   -z 2e5     # -> 134476³ −159380³ +117367³
./search_cubes -k 30 -d0 1 -d1 2000000 -z 3e8     # -> 2220422932³ −2218888517³ −283059965³

# the real thing
python3 make_wu.py plan --k 114 --d0 1 --d1 1e12 --z 5.4e13 --units 4096 > wu.txt
#   ... dispatch the commands in wu.txt ...
python3 make_wu.py verify --dir results/ --plan wu.txt
python3 st_cubes.py scan results/all.out
```

## Method used by `search_cubes.c`

Assume `|x| > |y| > |z|` and set `d = |x+y|`. Then `(x,y,z)` is a solution iff

1. `z³ ≡ k (mod d)`, and
2. `Δ(d,z) = 3d(4|k − z³| − d³)` is a perfect square,

with `x, y = (σd ± √Δ/(3d))/2`. Because `114 ≡ −3 (mod 9)` we get
`x ≡ y ≡ z ≡ −1 (mod 3)`, hence `3 ∤ d`, `sgn(z) = −(d|3)`, `sgn(x+y) = −sgn(z)`,
and `|z| > d/α` with `α = 2^(1/3) − 1`.

Implementation notes: segmented-sieve factorisation of `d`; cube roots mod `p`
via Adleman–Manders–Miller with Hensel lifting to prime powers; CRT over the
prime-power root sets; quadratic-residue sieve on `Δ` using auxiliary primes
`< 256`, with the allowed-residue sets precomputed once per `(p, d mod p, sgn z)`
rather than per `d`; CRT enumeration over the most restrictive auxiliary primes;
exact 256-bit `Δ` test and full re-verification of every hit before output.

**Validation.** Against exhaustive brute force over `|x|,|y|,|z| ≤ 1200` for
`k ∈ {3,12,21,30,39,48,57,66,75,84,93,102,114,120,129}`: zero missed solutions.
It also returns solutions whose *maximum* lies outside the brute-force box
(e.g. `48 = 1288³ − 1274³ − 410³`), which is the point of the method — it finds
everything with `min ≤ zmax` regardless of how large `max` is.

## Cost

Work per `d` is `∝ zmax/d`, so total work `∝ log(D1/D0)` — **split the `d` range
geometrically**, which `make_wu.py` does. A uniform split gives you one work unit
that runs for a year and a million that finish instantly.

Measured, single core (this machine), `k = 114` at fixed ratio `R = zmax/dmax = 54`:

| dmax | zmax | wall | candidates |
|---|---|---|---|
| 10⁶ | 5.4×10⁷ | 3.25 s | 2.2×10⁷ |
| 4×10⁶ | 2.2×10⁸ | 12.5 s | 8.6×10⁷ |
| 1.6×10⁷ | 8.6×10⁸ | 48.8 s | 3.4×10⁸ |

Clean linear scaling in `dmax`: ≈ **3.3 µs per unit of dmax**. Extrapolating to
the already-completed `dmax = 1.85×10¹⁷` sweep gives ≈ **2×10⁴ core-years** —
just to reproduce what is already known. Going one octave beyond it costs the
same again.

## Limitations — read before spending compute

1. **Use the reference implementation for a real run.**
   <https://github.com/AndrewVSutherland/SumsOfThreeCubes> is the Booker–Sutherland
   code, already proven on Charity Engine. It is roughly one to two orders of
   magnitude faster than this file, because it adds the cubic-reciprocity /
   mod-81k admissibility constraints (2–4×), incremental CRT enumeration, and
   dynamic auxiliary-prime selection.
2. **`d1 ≲ 10¹³` here.** This code factors `d` by sieving, so it needs primes up
   to `√d1`. Past ~10¹³ you must generate `d` multiplicatively from the admissible
   primes (those `p` for which `k` is a cubic residue) instead of factoring, as
   the reference implementation does. A serious 114 attempt needs `dmax ~ 10¹⁷–10¹⁸`.
3. **`zmax ≤ 4×10¹⁸`** — the exact `Δ` test is fixed 256-bit. Beyond that, widen
   `u256`.
4. **No error detection.** Booker–Sutherland deliberately refuse to make
   unconditional claims from volunteer hardware, and found real errors in 5 of
   155,579 nodes on ECC-free machines. Any negative result from this needs
   redundant assignment and prime-count checksums.

The genuinely reusable part of this directory is the reduction and the
`(x,y,z) ↔ (s,t,y)` dictionary. The searcher is here so the pipeline is
end-to-end testable, not because it is the fastest way to spend your cores.

---

## Running it on a Mac (Apple Silicon)

```sh
cd cubes114
chmod +x run_mac.sh

./run_mac.sh selftest              # ~1 min, proves toolchain + code
./run_mac.sh bench                 # ~2 min, measures YOUR single-core rate
caffeinate -i ./run_mac.sh run 114 1e10 5.4e11 6
```

`-march=native` is a GCC-ism and Apple clang rejects it on arm64; `run_mac.sh`
tries `-mcpu=native` and falls back to plain `-O3`. Everything is native arm64,
no Rosetta.

An 8-core M1 Pro is 6 performance + 2 efficiency cores, and the E-cores are
roughly 3x slower. Work is therefore handed out from a queue (`xargs -P`) with
`UNITS = 64 x JOBS`, so a slow core just takes fewer units. Use `JOBS=6` to stay
on P-cores and keep the machine usable; `JOBS=8` buys maybe 10-15% more and makes
the laptop unpleasant. Stay on wall power - macOS throttles hard on battery.

Reach, using a P-core rate of ~2 microseconds per unit of `dmax` (verify with
`bench`), at ratio `zmax/dmax = 54`:

| full-machine time | dmax reached | zmax reached |
|---|---|---|
| 1 hour | ~1.3x10^10 | ~7x10^11 |
| 1 day | ~3x10^11 | ~1.6x10^13 |
| 1 week | ~2x10^12 | ~1.1x10^14 |
| 1 month | ~9x10^12 | ~5x10^14 |

The completed 2020 Charity Engine sweep reached `dmax = 1.85x10^17`. A month of
your whole laptop therefore re-covers about **0.005%** of ground that is already
known to be empty. This machine is the right tool for validating the pipeline and
calibrating cost estimates; it is not a tool that can find a solution for 114.
