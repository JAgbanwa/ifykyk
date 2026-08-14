# Summary of changes for run f7b571b0-bfd5-40e2-b4ec-80e74469c765
All results are gathered in the single Lean file `RequestProject/BigFraction.lean`, which builds with no `sorry`, no added axioms, and no `native_decide` (only `propext`, `Classical.choice`, `Quot.sound`).
**The answer.** Write H = 176959370426063526189820447723837571181114689072145824174813. The two bounds in the problem are exactly 3·H and 2·H, and every coefficient of the numerator is divisible by H, with the denominator equal to H·(2t+1). So the expression reduces to
  y = P(s)/(2t+1),  P(s) = p₃s³+p₂s²+p₁s+p₀,  where p₃, p₂, p₁ are even and p₀ is odd.
Setting Q(a,b) = b³·P(a/b) ∈ ℤ, one gets y = d·Q(a,b) / (b³(2c+d)). Since H is prime (proved in the file), the admissible denominators are b ∈ {3, H, 3H} and d ∈ {2, H, 2H}, and:
1. **d = 2 and d = 2H are impossible.** In both cases 4 divides 2c+d, while b and Q(a,b) are odd, so d·Q(a,b) carries exactly one factor 2. Hence whenever y is an integer, t must have denominator exactly H, i.e. t = c/H with gcd(c,H)=1 (`den_t_eq_H`).
2. **Given t = c/H, y is an integer exactly when b³(2c+H) divides H·Q(a,b)** (`y_isInt_iff`, the main characterization). Explicitly, per denominator of s:
   - s = a/3 : iff (2c+H) ∣ Q(a,3)/27 (`y_isInt_iff_b_three`);
   - s = a/H : iff (2c+H) ∣ Q(a,H)/H² (`y_isInt_iff_b_H`);
   - s = a/(3H) : iff (2c+H) ∣ Q(a,3H)/(27H²) (`y_isInt_iff_b_threeH`).
   The three quotients are given as explicit integer cubics in a (`R3`, `RH`, `R3H`).
3. There are **infinitely many** such (s,t): any c with 2c+H = ±1 works for every admissible s; the file records one concrete instance, s = 1/3 and t = −88479685213031763094910223861918785590557344536072912087406/H, where y = 2317355092340780427302721112649244485507395154719055401102509725138072896539044486248905595959073544732342885405736789016782025542352371398991386017033191728589071584770541087115981 (`example_solution`).
The value t = −1/2 (where the given denominator vanishes) is excluded by the hypothesis 2c+d ≠ 0; this is stated in the docstrings. The problem's hypotheses gcd(a,b)=1 and (a,b) ≠ (c,d) are kept in the statements but are noted as not needed for the conclusions.
To make the sharp statement "the denominator of t is exactly H" available, the file also contains a small, reusable Pratt-certificate framework (a kernel-computable modular exponentiation with a correctness proof, plus a general certificate lemma on top of the Lucas test) and the full certificate tree proving that the 60-digit H is prime (`H_prime`).
