# Summary of changes for run c6d27d74-54bb-4df1-b9f2-230d5be5ffe2
I reworked the explicit data so that a₁ ≠ b₂, and reproved everything in Lean.
**New choice of constants.** For each digit size d ∈ {10,20,30,40,50} I take a₁ = 5^k, b₂ = 2·5^k = 2·a₁ (hence a₁ ≠ b₂), b₁ = 10^d − 1, and a₂ the unique admissible residue class mod b₂; all four numbers have exactly d digits.
| d | k | a₁ = 5^k | b₂ = 2·5^k | a₂ |
|---|---|---|---|---|
| 10 | 13 | 1220703125 | 2441406250 | 1628355764 |
| 20 | 28 | 37252902984619140625 | 74505805969238281250 | 52771027728679137014 |
| 30 | 42 | 227373675443232059478759765625 | 454747350886464118957519531250 | 416900266461691315814616637014 |
| 40 | 56 | 1387778780781445675529539585113525390625 | 2775557561562891351059079170227050781250 | 1774479435842646753915271218463542418264 |
| 50 | 71 | 42351647362715016953416125033982098102569580078125 | 84703294725430033906832250067964196205139160156250 | 89538054458658044004967802439384779389545085387014 |
with b₁ = 10^d − 1 in each case.
**What is proved (no `sorry`, only the standard axioms).**
- `RequestProject/Core.lean`: as before the identity 2·P(n) = 9(2n+1)³ − 1, P(n) ≠ 0, the 5-adic uniqueness `pow5_char`, and the impossibility result `not_forall_dvd_of_modEq`. Newly added: `two_dvd_P_iff` (P(n) is even exactly when n is) and `two_pow5_char`, the characterisation of divisibility of P(n) by 2·5^k — again exactly one residue class of n.
- `RequestProject/Answers.lean`: for each d, `char_d` (b₂ ∣ P n ↔ n ≡ a₂ (mod b₂), an iff, so the congruence on n is necessary and sufficient), `answer_d` (from 0 < x < b₁ with x ≡ a₁ (mod b₁), which pins x = a₁, and n ≡ a₂ (mod b₂), the fraction P(n)/x is an integer — a₁ = 5^k divides b₂ = 2·5^k which divides P(n)), and `digits_d` (each of a₁, b₁, a₂, b₂ lies in [10^(d−1), 10^d), together with the explicit statement a₁ ≠ b₂).
- `ANSWERS.md` was updated to the new table and now also records that P(n) is always coprime to 3 (it is not always coprime to 6 — e.g. P(0) = 4 — an inaccuracy in the earlier prose, now corrected).
The bound 0 < x < b₁ is still carried, since a congruence on x alone can never force x ∣ P(n) (`not_forall_dvd_of_modEq`).
The project builds cleanly, contains no `sorry`, and all work is committed and pushed.
# Summary of changes for run 911f5e4b-da5b-43e8-aee1-a07bc36a13a1
**Answer.** Write P(n) = 36n³ + 54n² + 27n + 4. The fraction P(n)/x is an integer exactly when x | P(n). Everything follows from the identity
    2·P(n) = 9·(2n+1)³ − 1,
which shows P(n) is never 0 and is always coprime to 6, and turns "N | P(n)" (for N coprime to 6) into solving 9·m³ ≡ 1 (mod N) with m = 2n+1. For N = 5^k the cubing map is injective on the units of Z/5^k (since gcd(3, φ(5^k)) = gcd(3, 4·5^(k−1)) = 1), so **exactly one** residue class of n mod 5^k works — the congruence on n is necessary and sufficient, not just sufficient.
**One important caveat, which is itself proved.** A congruence x ≡ a₁ (mod b₁) describes infinitely many x, including ones larger than |P(n)|; since P(n) ≠ 0, no such unbounded family can consist of divisors of P(n). This is formalized as `CubicFraction.not_forall_dvd_of_modEq`: for every a₁, b₁ > 0 and every n there is a positive x ≡ a₁ (mod b₁) with x ∤ P(n). Consequently the condition on x is stated as "x ≡ a₁ (mod b₁) together with 0 < x < b₁", which pins x = a₁.
**The requested data** (all of a₁, b₁, a₂, b₂ have exactly d digits; b₂ = a₁ = 5^k, b₁ = 10^d − 1):
| d | k | a₁ = b₂ = 5^k | a₂ |
|---|---|---|---|
| 10 | 14 | 6103515625 | 6511168264 |
| 20 | 28 | 37252902984619140625 | 15518124744059996389 |
| 30 | 42 | 227373675443232059478759765625 | 189526591018459256335856871389 |
| 40 | 57 | 6938893903907228377647697925567626953125 | 1774479435842646753915271218463542418264 |
| 50 | 71 | 42351647362715016953416125033982098102569580078125 | 47186407095943027051551677405402681286975505308889 |
**What is in the project.**
- `RequestProject/Core.lean`: the definition of P, the identity 2P(n) = 9(2n+1)³ − 1, P(n) ≠ 0, injectivity of cubing on the units of Z/5^k, uniqueness of the residue class (`pow5_dvd_P_unique`), the general characterisation `pow5_char`, and the impossibility result `not_forall_dvd_of_modEq`.
- `RequestProject/Answers.lean`: for each d ∈ {10,20,30,40,50}, `char_d` (b₂ | P(n) ↔ n ≡ a₂ (mod b₂)), `answer_d` (under the two congruences plus 0 < x < b₁, P(n) = x·q for an integer q), and `digits_d` (each constant lies in [10^(d−1), 10^d), i.e. has exactly d digits).
- `ANSWERS.md`: a readable summary of the mathematics and the data table.
The project builds cleanly with no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). All work is committed and pushed.
