import Mathlib
set_option maxRecDepth 100000
/-!
# Pratt primality certificates
A small amount of infrastructure for verifying primality of large numbers via the
Lucas test (`lucas_primality`), using a kernel-computable modular exponentiation.
-/
namespace Pratt
/-- Modular exponentiation by repeated squaring, with an explicit fuel argument so that
the definition is structurally recursive (and therefore reduces in the kernel). -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | fuel + 1, b, e =>
      if e = 0 then 1 % m
      else
        let r := powMod m fuel (b * b % m) (e / 2)
        if e % 2 = 1 then r * b % m else r
lemma powMod_eq (m : ℕ) : ∀ (fuel b e : ℕ), e < 2 ^ fuel → powMod m fuel b e = b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
      intro b e he
      have : e = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using he)
      subst this
      simp [powMod]
  | succ n ih =>
      intro b e he
      by_cases h0 : e = 0
      · subst h0; simp [powMod]
      · have hhalf : e / 2 < 2 ^ n := by
          have : e < 2 * 2 ^ n := by
            simpa [pow_succ, two_mul, Nat.mul_comm] using he
          omega
        have hr : powMod m n (b * b % m) (e / 2) = (b * b) ^ (e / 2) % m := by
          rw [ih (b * b % m) (e / 2) hhalf]
          exact (Nat.pow_mod (b * b) (e / 2) m).symm
        rcases Nat.even_or_odd e with hpar | hpar
        · have h2 : e % 2 = 0 := Nat.even_iff.mp hpar
          have he2 : 2 * (e / 2) = e := by omega
          simp only [powMod, if_neg h0, h2, hr]
          norm_num
          rw [← sq, ← pow_mul, he2]
        · have h2 : e % 2 = 1 := Nat.odd_iff.mp hpar
          have he2 : 2 * (e / 2) + 1 = e := by omega
          simp only [powMod, if_neg h0, h2, hr, if_pos]
          rw [Nat.mod_mul_mod, ← sq, ← pow_mul, ← pow_succ, he2]
lemma mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ (l : List ℕ), (∀ x ∈ l, Nat.Prime x) → q ∣ l.prod → q ∈ l := by
  intro l
  induction l with
  | nil => intro _ h; simp at h; exact absurd h hq.ne_one
  | cons x t ih =>
      intro hl h
      rw [List.prod_cons] at h
      rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
      · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq
          (hl x (List.mem_cons_self ..))).mp h1))
      · exact List.mem_cons.mpr (Or.inr (ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) h1))
/-- Pratt certificate: if `l` is a list of primes with product `p - 1` and `a` is a witness
whose order is exactly `p - 1`, then `p` is prime. -/
theorem prime_of_pratt (p a fuel : ℕ) (l : List ℕ)
    (hfuel : p - 1 < 2 ^ fuel)
    (hl : ∀ x ∈ l, Nat.Prime x)
    (hprod : l.prod = p - 1)
    (h1 : powMod p fuel a (p - 1) = 1 % p)
    (h2 : ∀ x ∈ l, powMod p fuel a ((p - 1) / x) ≠ 1 % p) :
    p.Prime := by
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · have hmod : a ^ (p - 1) % p = 1 % p := by rw [← powMod_eq p fuel a (p - 1) hfuel, h1]
    have : ((a ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
    push_cast at this
    exact this
  · intro q hq hqd hcon
    have hmem : q ∈ l := mem_of_prime_dvd_prod hq l hl (by rw [hprod]; exact hqd)
    have hlt : (p - 1) / q < 2 ^ fuel := lt_of_le_of_lt (Nat.div_le_self _ _) hfuel
    refine h2 q hmem ?_
    rw [powMod_eq p fuel a _ hlt]
    refine (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_
    push_cast
    exact hcon
/-! ### A Pratt certificate tree for
`H = 176959370426063526189820447723837571181114689072145824174813` -/
theorem prime_18445477 : Nat.Prime 18445477 := by
  refine prime_of_pratt 18445477 6 25 [2, 2, 3, 7, 17, 12917] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> norm_num
theorem prime_664037173 : Nat.Prime 664037173 := by
  refine prime_of_pratt 664037173 2 30 [2, 2, 3, 3, 18445477] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_18445477 | norm_num
theorem prime_19921115191 : Nat.Prime 19921115191 := by
  refine prime_of_pratt 19921115191 3 35 [2, 3, 5, 664037173] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_664037173 | norm_num
theorem prime_12663577 : Nat.Prime 12663577 := by
  refine prime_of_pratt 12663577 17 24 [2, 2, 2, 3, 3, 19, 9257] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> norm_num
theorem prime_3469820099 : Nat.Prime 3469820099 := by
  refine prime_of_pratt 3469820099 2 32 [2, 137, 12663577] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_12663577 | norm_num
theorem prime_452388057439 : Nat.Prime 452388057439 := by
  refine prime_of_pratt 452388057439 13 39 [2, 3, 263909, 285697] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> norm_num
theorem prime_17851866427 : Nat.Prime 17851866427 := by
  refine prime_of_pratt 17851866427 2 35 [2, 3, 3, 3, 1873, 176503] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> norm_num
theorem prime_164592833 : Nat.Prime 164592833 := by
  refine prime_of_pratt 164592833 3 28 [2, 2, 2, 2, 2, 2, 101, 25463] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> norm_num
theorem prime_329185667 : Nat.Prime 329185667 := by
  refine prime_of_pratt 329185667 2 29 [2, 164592833] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_164592833 | norm_num
theorem prime_38185537373 : Nat.Prime 38185537373 := by
  refine prime_of_pratt 38185537373 2 36 [2, 2, 29, 329185667] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_329185667 | norm_num
theorem prime_4090098675756074857627 : Nat.Prime 4090098675756074857627 := by
  refine prime_of_pratt 4090098675756074857627 2 72 [2, 3, 17851866427, 38185537373] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_17851866427 | exact prime_38185537373 | norm_num
theorem prime_202108135963810683014780579 : Nat.Prime 202108135963810683014780579 := by
  refine prime_of_pratt 202108135963810683014780579 2 88 [2, 31, 797, 4090098675756074857627] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_4090098675756074857627 | norm_num
theorem prime_176959370426063526189820447723837571181114689072145824174813 : Nat.Prime 176959370426063526189820447723837571181114689072145824174813 := by
  refine prime_of_pratt 176959370426063526189820447723837571181114689072145824174813 2 197 [2, 2, 7, 3469820099, 19921115191, 452388057439, 202108135963810683014780579] (by norm_num) ?_ (by decide) (by decide)
    (by decide)
  intro x hx
  fin_cases hx <;> first | exact prime_3469820099 | exact prime_19921115191 | exact prime_452388057439 | exact prime_202108135963810683014780579 | norm_num
end Pratt
/-!
# When is the given big fraction an integer?
We study the expression of the problem
```
y = (c₃ s³ + c₂ s² + c₁ s + c₀) / (M t + H)
```
for `s = a/b` and `t = c/d` rational, in lowest terms and not integers, with
`b ∣ 3*H = 530878111278190578569461343171512713543344067216437472524439` and
`d ∣ 2*H = 353918740852127052379640895447675142362229378144291648349626`.
The structural facts behind everything are:
* `H = 176959370426063526189820447723837571181114689072145824174813` is prime
  (proved above by a Pratt certificate), `M = 2*H`, and `cᵢ = H * pᵢ`;
* hence `y = P(s) / (2t+1)` with `P(s) = p₃s³ + p₂s² + p₁s + p₀`, where `p₃, p₂, p₁` are even
  and `p₀` is odd.
**Answer.** Since `H` is prime, the admissible denominators are `b ∈ {3, H, 3H}` and
`d ∈ {2, H, 2H}`. Writing `Q a b = b³·P(a/b) ∈ ℤ` one has `y = d·Q a b / (b³(2c+d))`, and:
* `d = 2` and `d = 2*H` are impossible (`not_two_dvd_d`): then `2c+d` is divisible by `4`
  while `d·Q a b` has exactly one factor `2`, since `Q a b` and `b` are odd.
  So the denominator of `t` must be exactly `H`, i.e. `t = c/H` (`den_t_eq_H`).
* Given `t = c/H`, `y` is an integer iff `b³(2c+H) ∣ H·Q a b` (`y_isInt_iff`).
  Explicitly (`y_isInt_iff_b_three`, `y_isInt_iff_b_H`, `y_isInt_iff_b_threeH`):
  - `b = 3`   : iff `(2c+H) ∣ Q a 3 / 27`;
  - `b = H`   : iff `(2c+H) ∣ Q a H / H²`;
  - `b = 3*H` : iff `(2c+H) ∣ Q a (3H) / (27H²)`.
  In each case `a` is otherwise arbitrary, and there are infinitely many solutions: e.g.
  `c = (1-H)/2` makes `2c+H = 1` (see `example_solution`).
The value `t = -1/2`, where the denominator `M t + H` vanishes, is excluded throughout by the
hypothesis `2*c + d ≠ 0`.
-/
namespace BigFraction
/-- The 60-digit number `H`; it is prime, see `H_prime`. -/
def H : ℤ := 176959370426063526189820447723837571181114689072145824174813
/-- Cubic coefficient of the reduced numerator `P`. -/
def p3 : ℤ :=
  30437809455704281067731907337009388001148355335052348115349102798464506349052579132691458602436751108516074999396844589868
/-- Quadratic coefficient of the reduced numerator `P`. -/
def p2 : ℤ :=
  38496673852220855875039119077718446186005851033662206069600477255798970180570780789528589605761748989739301441450061000092
/-- Linear coefficient of the reduced numerator `P`. -/
def p1 : ℤ :=
  16229747630612620894474342491658416711249687684986919906521261098750452308113294600443827634324933113973871986598038043716
/-- Constant coefficient of the reduced numerator `P`. -/
def p0 : ℤ :=
  2280757286240027394511200147901903974616930323613078576420036741772222552767550759907580816340721379961227070708809057093
/-- The expression `y` of the problem, as a function of the two rationals `s` and `t`. -/
noncomputable def y (s t : ℚ) : ℚ :=
  (5386255598429912910239991074883103648061323608347515713067104506907275944285878462789841452986266125005845596825628779494465555970916820770687828281560445713580845857529504520594684 * s^3
    + 6812347168386504364564397888712133441306659545486542739467076752649122734543687696820388736586306024705642039157739295712828518798880977420816988175841637415790459974110929417082796 * s^2
    + 2872005922887105612204712888576895642803577224840059660525955764481773178812678494861246411912387442454262975294561586568820236883258414904154274451272523530538639364401666520125108 * s
    + 403601373467692408273995159382149494499487848483215368650586145686569090715672337841415767442159797280078496814999716951880794271356612614897783688494744701337220471456567329598609)
  / (353918740852127052379640895447675142362229378144291648349626 * t
    + 176959370426063526189820447723837571181114689072145824174813)
/-- `Q a b = b³ · P(a/b)` is the (integral) numerator of `P` evaluated at `a/b`. -/
def Q (a b : ℤ) : ℤ := p3 * a^3 + p2 * a^2 * b + p1 * a * b^2 + p0 * b^3
lemma H_pos : 0 < H := by norm_num [H]
lemma H_ne_zero : (H : ℚ) ≠ 0 := by norm_num [H]
/-- After cancelling the common factor `H`, `y` is `P(s)/(2t+1)`. -/
lemma y_eq (s t : ℚ) :
    y s t = ((p3 : ℚ) * s^3 + p2 * s^2 + p1 * s + p0) / (2 * t + 1) := by
  have hnum :
      (5386255598429912910239991074883103648061323608347515713067104506907275944285878462789841452986266125005845596825628779494465555970916820770687828281560445713580845857529504520594684 * s^3
        + 6812347168386504364564397888712133441306659545486542739467076752649122734543687696820388736586306024705642039157739295712828518798880977420816988175841637415790459974110929417082796 * s^2
        + 2872005922887105612204712888576895642803577224840059660525955764481773178812678494861246411912387442454262975294561586568820236883258414904154274451272523530538639364401666520125108 * s
        + 403601373467692408273995159382149494499487848483215368650586145686569090715672337841415767442159797280078496814999716951880794271356612614897783688494744701337220471456567329598609 : ℚ)
        = (H : ℚ) * ((p3 : ℚ) * s^3 + p2 * s^2 + p1 * s + p0) := by
    simp only [H, p3, p2, p1, p0, Int.cast_ofNat]
    ring
  have hden :
      (353918740852127052379640895447675142362229378144291648349626 * t
        + 176959370426063526189820447723837571181114689072145824174813 : ℚ)
        = (H : ℚ) * (2 * t + 1) := by
    simp only [H]
    push_cast
    ring
  rw [y, hnum, hden, mul_div_mul_left _ _ H_ne_zero]
/-- Value of `y` at `s = a/b`, `t = c/d`. -/
lemma y_at (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) (hcd : 2 * c + d ≠ 0) :
    y ((a : ℚ) / b) ((c : ℚ) / d) = ((d * Q a b : ℤ) : ℚ) / ((b^3 * (2 * c + d) : ℤ) : ℚ) := by
  have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hcd' : ((2 * c + d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hcd
  have h1 : (2 : ℚ) * ((c : ℚ) / (d : ℚ)) + 1 ≠ 0 := by
    push_cast at hcd'
    intro h
    apply hcd'
    field_simp at h
    linarith [h]
  have h2 : ((b^3 * (2 * c + d) : ℤ) : ℚ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (pow_ne_zero _ hb') (by push_cast at hcd'; exact hcd')
  rw [y_eq, div_eq_div_iff h1 h2]
  simp only [Q]
  push_cast
  field_simp
/-- Integrality of `y` at `s = a/b`, `t = c/d` is a divisibility statement. -/
lemma y_isInt_iff_dvd (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) (hnz : 2 * c + d ≠ 0) :
    (∃ k : ℤ, y ((a : ℚ) / b) ((c : ℚ) / d) = (k : ℚ)) ↔ (b^3 * (2 * c + d)) ∣ (d * Q a b) := by
  have h2 : ((b^3 * (2 * c + d) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (pow_ne_zero _ hb) hnz
  rw [y_at a b c d hb hd hnz]
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_iff h2] at hk
    have hk' : d * Q a b = k * (b^3 * (2 * c + d)) := by exact_mod_cast hk
    exact ⟨k, by rw [hk', mul_comm]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [div_eq_iff h2, hk]
    push_cast
    ring
/-- Any divisor of `3*H` is odd. -/
lemma odd_of_dvd_threeH {b : ℤ} (hb : b ∣ 3 * H) : ¬ (2 ∣ b) := by
  intro h
  have : (2 : ℤ) ∣ 3 * H := h.trans hb
  rw [H] at this
  omega
lemma p3_even : p3 = 2 * 15218904727852140533865953668504694000574177667526174057674551399232253174526289566345729301218375554258037499698422294934 := by
  norm_num [p3]
lemma p2_even : p2 = 2 * 19248336926110427937519559538859223093002925516831103034800238627899485090285390394764294802880874494869650720725030500046 := by
  norm_num [p2]
lemma p1_even : p1 = 2 * 8114873815306310447237171245829208355624843842493459953260630549375226154056647300221913817162466556986935993299019021858 := by
  norm_num [p1]
lemma p0_odd : ¬ ((2 : ℤ) ∣ p0) := by
  rw [p0]
  omega
/-- `Q a b` is odd whenever `b` is odd. -/
lemma Q_odd {a b : ℤ} (hb : ¬ (2 ∣ b)) : ¬ (2 ∣ Q a b) := by
  intro h
  have key : (2 : ℤ) ∣ p0 * b ^ 3 := by
    have hQ : p0 * b ^ 3 = Q a b - 2 *
        (15218904727852140533865953668504694000574177667526174057674551399232253174526289566345729301218375554258037499698422294934 * a^3
          + 19248336926110427937519559538859223093002925516831103034800238627899485090285390394764294802880874494869650720725030500046 * a^2 * b
          + 8114873815306310447237171245829208355624843842493459953260630549375226154056647300221913817162466556986935993299019021858 * a * b^2) := by
      simp only [Q, p3_even, p2_even, p1_even]
      ring
    rw [hQ]
    exact dvd_sub h (Dvd.intro _ rfl)
  rcases (Int.prime_two.dvd_mul).mp key with h1 | h1
  · exact p0_odd h1
  · exact hb (Int.prime_two.dvd_of_dvd_pow h1)
/-- The denominator of `t` cannot be even: this is the key obstruction. -/
lemma not_two_dvd_d {a b c d : ℤ} (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hb : b ∣ 3 * H) (hd : d ∣ 2 * H)
    (hcd : Int.gcd c d = 1) (hnz : 2 * c + d ≠ 0)
    (hy : ∃ k : ℤ, y ((a : ℚ) / b) ((c : ℚ) / d) = (k : ℚ)) : ¬ (2 ∣ d) := by
  rintro ⟨e, rfl⟩
  -- `e` divides `H`, hence is odd
  have he : e ∣ H := by
    rcases hd with ⟨u, hu⟩
    exact ⟨u, by linarith [hu]⟩
  have heodd : ¬ (2 ∣ e) := by
    intro h2
    have : (2 : ℤ) ∣ H := h2.trans he
    rw [H] at this
    omega
  -- `c` is odd since `gcd c (2*e) = 1`
  have hcodd : ¬ (2 ∣ c) := by
    intro h2
    have hco : IsCoprime c (2 * e) := Int.isCoprime_iff_gcd_eq_one.mpr hcd
    have : IsUnit (2 : ℤ) := hco.isUnit_of_dvd' h2 (Dvd.intro e rfl)
    rw [Int.isUnit_iff] at this
    omega
  -- hence `c + e` is even and `4 ∣ 2*c + 2*e`
  obtain ⟨g, hg⟩ : (2 : ℤ) ∣ c + e := by omega
  have hbodd : ¬ (2 ∣ b) := odd_of_dvd_threeH hb
  have hQodd : ¬ (2 ∣ Q a b) := Q_odd hbodd
  rw [y_isInt_iff_dvd a b c (2 * e) hb0 hd0 hnz] at hy
  obtain ⟨k, hk⟩ := hy
  -- `2*e*Q = k*b³*(4g)` forces `e*Q` to be even
  have h4 : 2 * e * Q a b = b^3 * (4 * g) * k := by
    rw [hk, show (2 * c + 2 * e : ℤ) = 4 * g from by omega]
  have h5 : (2 : ℤ) * (e * Q a b) = 2 * (2 * (b^3 * g * k)) := by
    rw [← mul_assoc, h4]; ring
  have h6 : (2 : ℤ) ∣ e * Q a b := ⟨b^3 * g * k, mul_left_cancel₀ two_ne_zero h5⟩
  rcases (Int.prime_two.dvd_mul).mp h6 with h1 | h1
  · exact heodd h1
  · exact hQodd h1
/-- `H` is prime (verified by a Pratt certificate). -/
lemma H_prime : Prime (H : ℤ) := by
  rw [Int.prime_iff_natAbs_prime, H]
  exact Pratt.prime_176959370426063526189820447723837571181114689072145824174813
/-- The positive divisors of `H` are `1` and `H`. -/
lemma eq_one_or_H_of_dvd {m : ℤ} (hm : 0 < m) (h : m ∣ H) : m = 1 ∨ m = H := by
  obtain ⟨e, he⟩ := h
  rcases H_prime.irreducible.isUnit_or_isUnit he with hu | hu
  · rw [Int.isUnit_iff] at hu; omega
  · rw [Int.isUnit_iff] at hu
    have := H_pos
    rcases hu with rfl | rfl <;> omega
/-- The admissible denominators for `s`. -/
lemma b_cases {b : ℤ} (hb : 1 < b) (hdvd : b ∣ 3 * H) : b = 3 ∨ b = H ∨ b = 3 * H := by
  by_cases h3 : (3 : ℤ) ∣ b
  · obtain ⟨m, rfl⟩ := h3
    have hm : m ∣ H := (mul_dvd_mul_iff_left (by norm_num : (3:ℤ) ≠ 0)).mp hdvd
    have hmpos : 0 < m := by nlinarith
    rcases eq_one_or_H_of_dvd hmpos hm with rfl | rfl
    · exact Or.inl (by ring)
    · exact Or.inr (Or.inr rfl)
  · have hco : IsCoprime b (3 : ℤ) :=
      ((Int.prime_three.coprime_iff_not_dvd).mpr h3).symm
    have : b ∣ H := hco.dvd_of_dvd_mul_left hdvd
    rcases eq_one_or_H_of_dvd (by omega) this with rfl | rfl
    · omega
    · exact Or.inr (Or.inl rfl)
/-- **Main result.**
Let `s = a/b` and `t = c/d` be rationals in lowest terms which are not integers
(`1 < b`, `1 < d`), with `b ∣ 3*H = 530878111278190578569461343171512713543344067216437472524439` and
`d ∣ 2*H = 353918740852127052379640895447675142362229378144291648349626`, and assume
`2*c + d ≠ 0` (i.e. `t ≠ -1/2`, where the fraction is undefined).
Then `y` is an integer if and only if the denominator of `t` is exactly the prime
`H = 176959370426063526189820447723837571181114689072145824174813` and
`b³ * (2*c + H)` divides `H * Q a b`.
The hypotheses `Int.gcd a b = 1` and `(a, b) ≠ (c, d)` from the problem statement are
included, but turn out not to be needed. -/
theorem y_isInt_iff (a b c d : ℤ) (hb : 1 < b) (hd : 1 < d)
    (hab : Int.gcd a b = 1) (hcd : Int.gcd c d = 1) (hne : (a, b) ≠ (c, d))
    (hbH : b ∣ 3 * H) (hdH : d ∣ 2 * H) (hnz : 2 * c + d ≠ 0) :
    (∃ k : ℤ, y ((a : ℚ) / b) ((c : ℚ) / d) = (k : ℚ)) ↔
      d = H ∧ (b ^ 3 * (2 * c + H)) ∣ (H * Q a b) := by
  have hb0 : b ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  constructor
  · intro hy
    have hodd : ¬ (2 ∣ d) := not_two_dvd_d hb0 hd0 hbH hdH hcd hnz hy
    have hdvdH : d ∣ H := by
      obtain ⟨u, hu⟩ := hdH
      have h2u : (2 : ℤ) ∣ u := by
        rcases (Int.prime_two.dvd_mul).mp (⟨H, hu.symm⟩ : (2:ℤ) ∣ d * u) with h | h
        · exact absurd h hodd
        · exact h
      obtain ⟨v, rfl⟩ := h2u
      exact ⟨v, by linarith [hu]⟩
    have hdeq : d = H := by
      rcases eq_one_or_H_of_dvd (by omega) hdvdH with h | h
      · omega
      · exact h
    refine ⟨hdeq, ?_⟩
    have hdvd := (y_isInt_iff_dvd a b c d hb0 hd0 hnz).mp hy
    rwa [hdeq] at hdvd
  · rintro ⟨rfl, h⟩
    exact (y_isInt_iff_dvd a b c H hb0 hd0 hnz).mpr h
/-- Consequence: whenever `y` is an integer, the denominator of `t` must be the prime `H`,
i.e. `t = c/H`; in particular `t` can never have denominator `2` or `2*H`. -/
theorem den_t_eq_H (a b c d : ℤ) (hb : 1 < b) (hd : 1 < d)
    (hcd : Int.gcd c d = 1) (hbH : b ∣ 3 * H) (hdH : d ∣ 2 * H) (hnz : 2 * c + d ≠ 0)
    (hy : ∃ k : ℤ, y ((a : ℚ) / b) ((c : ℚ) / d) = (k : ℚ)) : d = H := by
  have hb0 : b ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have hodd : ¬ (2 ∣ d) := not_two_dvd_d hb0 hd0 hbH hdH hcd hnz hy
  have hdvdH : d ∣ H := by
    obtain ⟨u, hu⟩ := hdH
    have h2u : (2 : ℤ) ∣ u := by
      rcases (Int.prime_two.dvd_mul).mp (⟨H, hu.symm⟩ : (2:ℤ) ∣ d * u) with h | h
      · exact absurd h hodd
      · exact h
    obtain ⟨v, rfl⟩ := h2u
    exact ⟨v, by linarith [hu]⟩
  rcases eq_one_or_H_of_dvd (by omega) hdvdH with h | h
  · omega
  · exact h
/-! ### Making the divisibility condition explicit in each of the three cases for `b` -/
/-- `Q a 3 / 27`. -/
def R3 (a : ℤ) : ℤ :=
  1127326276137195595101181753222569925968457605001938819087003807350537272187132560470054022312472263278373148125809058884 * a ^ 3
    + 4277408205802317319448791008635382909556205670406911785511164139533218908952308976614287733973527665526589049050006777788 * a ^ 2
    + 5409915876870873631491447497219472237083229228328973302173753699583484102704431533481275878108311037991290662199346014572 * a
    + p0
/-- `Q a H / H²`. -/
def RH (a : ℤ) : ℤ :=
  972 * a ^ 3
    + 217545269061100022185621444138581819617668928278210456684356684 * a ^ 2
    + p1 * a + p0 * H
/-- `Q a (3*H) / (27*H²)`. -/
def R3H (a : ℤ) : ℤ :=
  36 * a ^ 3
    + 24171696562344446909513493793175757735296547586467828520484076 * a ^ 2
    + 5409915876870873631491447497219472237083229228328973302173753699583484102704431533481275878108311037991290662199346014572 * a
    + p0 * H
lemma Q_three (a : ℤ) : Q a 3 = 27 * R3 a := by
  simp only [Q, R3, p3, p2, p1]
  ring
lemma Q_H (a : ℤ) : Q a H = H ^ 2 * RH a := by
  simp only [Q, RH, p3, p2, H]
  ring
lemma Q_threeH (a : ℤ) : Q a (3 * H) = 27 * H ^ 2 * R3H a := by
  simp only [Q, R3H, p3, p2, p1, H]
  ring
/-- Since `gcd (c, H) = 1` and `H` is prime, `2*c + H` is coprime to `H`. -/
lemma dvd_H_mul_iff {c m : ℤ} (hc : Int.gcd c H = 1) :
    (2 * c + H) ∣ H * m ↔ (2 * c + H) ∣ m := by
  have hnd : ¬ (H ∣ 2 * c + H) := by
    intro hdvd
    have h2c : H ∣ 2 * c := by
      have := dvd_sub hdvd (dvd_refl H)
      simpa using this
    have hco : IsCoprime c H := Int.isCoprime_iff_gcd_eq_one.mpr hc
    rcases H_prime.dvd_mul.mp h2c with h | h
    · rw [H] at h; omega
    · have : IsUnit (H : ℤ) := hco.symm.isUnit_of_dvd' dvd_rfl h
      rw [Int.isUnit_iff, H] at this
      omega
  have hco : IsCoprime (2 * c + H) H :=
    ((H_prime.coprime_iff_not_dvd).mpr hnd).symm
  exact ⟨fun h => hco.dvd_of_dvd_mul_left h, fun h => h.mul_left H⟩
/-- Case `b = 3`: `y` is an integer iff `t = c/H` and `2*c + H` divides `Q a 3 / 27`.
The coprimality hypothesis on `a` is not needed. -/
theorem y_isInt_iff_b_three (a c d : ℤ) (hd : 1 < d)
    (hab : Int.gcd a 3 = 1) (hcd : Int.gcd c d = 1)
    (hdH : d ∣ 2 * H) (hnz : 2 * c + d ≠ 0) :
    (∃ k : ℤ, y ((a : ℚ) / 3) ((c : ℚ) / d) = (k : ℚ)) ↔ d = H ∧ (2 * c + H) ∣ R3 a := by
  have hb0 : (3 : ℤ) ≠ 0 := by norm_num
  have hd0 : d ≠ 0 := by omega
  rw [show ((3 : ℚ)) = (((3 : ℤ) : ℚ)) by norm_num, y_isInt_iff_dvd a 3 c d hb0 hd0 hnz]
  constructor
  · intro hdvd
    have hdeq : d = H :=
      den_t_eq_H a 3 c d (by norm_num) hd hcd (by rw [H]; norm_num) hdH hnz
        ((y_isInt_iff_dvd a 3 c d hb0 hd0 hnz).mpr hdvd)
    subst hdeq
    refine ⟨rfl, ?_⟩
    rw [Q_three] at hdvd
    have h27 : (3 : ℤ) ^ 3 * (2 * c + H) ∣ 3 ^ 3 * (H * R3 a) := by
      convert hdvd using 1; ring
    exact (dvd_H_mul_iff hcd).mp ((mul_dvd_mul_iff_left (by norm_num : (3:ℤ)^3 ≠ 0)).mp h27)
  · rintro ⟨rfl, h⟩
    rw [Q_three]
    obtain ⟨w, hw⟩ := (dvd_H_mul_iff hcd).mpr h
    exact ⟨w, by rw [show (H : ℤ) * (27 * R3 a) = 27 * (H * R3 a) from by ring, hw]; ring⟩
/-- Case `b = H`: `y` is an integer iff `t = c/H` and `2*c + H` divides `Q a H / H²`.
The coprimality hypothesis on `a` is not needed. -/
theorem y_isInt_iff_b_H (a c d : ℤ) (hd : 1 < d)
    (hab : Int.gcd a H = 1) (hcd : Int.gcd c d = 1)
    (hdH : d ∣ 2 * H) (hnz : 2 * c + d ≠ 0) :
    (∃ k : ℤ, y ((a : ℚ) / (H : ℤ)) ((c : ℚ) / d) = (k : ℚ)) ↔
      d = H ∧ (2 * c + H) ∣ RH a := by
  have hb0 : (H : ℤ) ≠ 0 := by have := H_pos; omega
  have hd0 : d ≠ 0 := by omega
  rw [y_isInt_iff_dvd a H c d hb0 hd0 hnz]
  constructor
  · intro hdvd
    have hdeq : d = H :=
      den_t_eq_H a H c d (by have := H_pos; rw [H]; norm_num) hd hcd ⟨3, by ring⟩ hdH hnz
        ((y_isInt_iff_dvd a H c d hb0 hd0 hnz).mpr hdvd)
    subst hdeq
    refine ⟨rfl, ?_⟩
    rw [Q_H] at hdvd
    have h3 : (H : ℤ) ^ 3 * (2 * c + H) ∣ H ^ 3 * (RH a) := by
      convert hdvd using 1; ring
    exact (mul_dvd_mul_iff_left (pow_ne_zero 3 hb0)).mp h3
  · rintro ⟨rfl, h⟩
    rw [Q_H]
    obtain ⟨w, hw⟩ := h
    exact ⟨w, by rw [hw]; ring⟩
/-- Case `b = 3*H`: `y` is an integer iff `t = c/H` and `2*c + H` divides `Q a (3H) / (27H²)`.
The coprimality hypothesis on `a` is not needed. -/
theorem y_isInt_iff_b_threeH (a c d : ℤ) (hd : 1 < d)
    (hab : Int.gcd a (3 * H) = 1) (hcd : Int.gcd c d = 1)
    (hdH : d ∣ 2 * H) (hnz : 2 * c + d ≠ 0) :
    (∃ k : ℤ, y ((a : ℚ) / ((3 * H : ℤ) : ℚ)) ((c : ℚ) / d) = (k : ℚ)) ↔
      d = H ∧ (2 * c + H) ∣ R3H a := by
  have hb0 : (3 * H : ℤ) ≠ 0 := by have := H_pos; omega
  have hd0 : d ≠ 0 := by omega
  rw [y_isInt_iff_dvd a (3 * H) c d hb0 hd0 hnz]
  constructor
  · intro hdvd
    have hdeq : d = H :=
      den_t_eq_H a (3 * H) c d (by have := H_pos; rw [H]; norm_num) hd hcd dvd_rfl hdH hnz
        ((y_isInt_iff_dvd a (3 * H) c d hb0 hd0 hnz).mpr hdvd)
    subst hdeq
    refine ⟨rfl, ?_⟩
    rw [Q_threeH] at hdvd
    have h3 : (27 * H ^ 3) * (2 * c + H) ∣ (27 * H ^ 3) * (R3H a) := by
      convert hdvd using 1; ring
    exact (mul_dvd_mul_iff_left (by have := H_pos; positivity : (27 * H ^ 3 : ℤ) ≠ 0)).mp h3
  · rintro ⟨rfl, h⟩
    rw [Q_threeH]
    obtain ⟨w, hw⟩ := h
    exact ⟨w, by rw [hw]; ring⟩
/-- The set of solutions is non-empty: for `s = 1/3` and
`t = -88479685213031763094910223861918785590557344536072912087406 / H`
(so that `2*c + H = 1`), `y` is an integer. -/
theorem example_solution :
    y (1 / 3)
      (-88479685213031763094910223861918785590557344536072912087406 /
        176959370426063526189820447723837571181114689072145824174813) =
      2317355092340780427302721112649244485507395154719055401102509725138072896539044486248905595959073544732342885405736789016782025542352371398991386017033191728589071584770541087115981 := by
  rw [y_eq]
  norm_num [p3, p2, p1, p0]
end BigFraction
