# When is `(36n³ + 54n² + 27n + 4)/x` an integer?
Write `P(n) = 36n³ + 54n² + 27n + 4`. The fraction `P(n)/x` is an integer exactly when
`x | P(n)`.
## The structure behind the answer
The key identity (proved as `CubicFraction.two_mul_P`) is
    2·P(n) = 9·(2n+1)³ − 1 .
Consequences:
* `P(n)` is never `0` (`CubicFraction.P_ne_zero`), and it is always coprime to `3`.
* For a modulus `N` coprime to `6`, `N | P(n)` is equivalent to solving
  `9·m³ ≡ 1 (mod N)` with `m = 2n + 1`.
* For `N = 5^k` the cubing map is injective on the units of `Z/5^k`, because
  `gcd(3, φ(5^k)) = gcd(3, 4·5^(k−1)) = 1`. Hence there is **exactly one** residue class
  of `n` modulo `5^k` with `5^k | P(n)` (`CubicFraction.pow5_dvd_P_unique`,
  `CubicFraction.pow5_char`).
* Moreover `P(n)` is even exactly when `n` is even (`CubicFraction.two_dvd_P_iff`), so for
  the modulus `2·5^k` there is again exactly one admissible residue class of `n`
  (`CubicFraction.two_pow5_char`).
## One caveat about a congruence on `x`
A congruence `x ≡ a₁ (mod b₁)` describes infinitely many `x`, including arbitrarily large
ones. Since `P(n)` is a fixed nonzero integer, no such unbounded family can consist of
divisors of `P(n)`. This is proved in `CubicFraction.not_forall_dvd_of_modEq`:
    for all a₁, b₁, n with b₁ > 0 there is x > 0 with x ≡ a₁ (mod b₁) and x ∤ P(n).
So the condition on `x` is stated together with the range `0 < x < b₁`, which (with
`0 < a₁ < b₁`) pins `x = a₁`. The condition on `n`, by contrast, is a genuine congruence
that is both necessary and sufficient.
## The explicit data (all four constants have exactly d digits, and `a₁ ≠ b₂`)
Here `a₁ = 5^k`, `b₂ = 2·5^k = 2·a₁` (so `a₁ ≠ b₂`), and `b₁ = 10^d − 1`.
| d | k | a₁ = 5^k | b₂ = 2·5^k | a₂ |
|---|---|---|---|---|
| 10 | 13 | 1220703125 | 2441406250 | 1628355764 |
| 20 | 28 | 37252902984619140625 | 74505805969238281250 | 52771027728679137014 |
| 30 | 42 | 227373675443232059478759765625 | 454747350886464118957519531250 | 416900266461691315814616637014 |
| 40 | 56 | 1387778780781445675529539585113525390625 | 2775557561562891351059079170227050781250 | 1774479435842646753915271218463542418264 |
| 50 | 71 | 42351647362715016953416125033982098102569580078125 | 84703294725430033906832250067964196205139160156250 | 89538054458658044004967802439384779389545085387014 |
and `b₁ = 10^d − 1` in each case (9999999999, 99999999999999999999, …).
For each `d` the file `RequestProject/Answers.lean` contains:
* `char_d`  : for every integer `n`,  `b₂ | P(n)  ↔  n ≡ a₂ (mod b₂)`;
* `answer_d`: if `0 < x < b₁`, `x ≡ a₁ (mod b₁)` and `n ≡ a₂ (mod b₂)`, then
  `P(n) = x·q` for some integer `q`, i.e. the fraction is an integer
  (here `x = a₁ = 5^k` divides `b₂ = 2·5^k`, which divides `P(n)`);
* `digits_d`: each of `a₁, b₁, a₂, b₂` lies in `[10^(d−1), 10^d)`, i.e. has exactly `d`
  digits, and `a₁ ≠ b₂`.
All statements are proved in Lean 4 with Mathlib, with no `sorry` and no extra axioms.
