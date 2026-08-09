import Mathlib
/-!
# Integrality of `(36 n^3 + 54 n^2 + 27 n + 4) / x`
Write `P n = 36 n^3 + 54 n^2 + 27 n + 4`.  The fraction `P n / x` is an integer exactly
when `x ∣ P n`.
The basic identity is
  `2 * P n = 9 * (2 n + 1)^3 - 1`,
so `P n` is never zero (and always coprime to `3`), and divisibility of `P n` by a modulus `N` coprime to `6` amounts
to solving `9 * m^3 ≡ 1 (mod N)` with `m = 2 n + 1`.
For `N = 5^k` the cubing map is injective on the units of `ZMod (5^k)` (because `3` is
coprime to `φ(5^k) = 4 * 5^(k-1)`), so there is at most **one** residue class of `n`
modulo `5^k` with `5^k ∣ P n`.  This is `pow5_dvd_P_unique`, packaged as the
characterisation `pow5_char`.
The file also records `not_forall_dvd_of_modEq`: no congruence condition
`x ≡ a₁ (mod b₁)` on an *unbounded* set of `x` can force `x ∣ P n`, since the progression
contains arbitrarily large integers while `P n` is a fixed nonzero number.  Hence a
condition on `x` of the form `x ≡ a₁ (mod b₁)` has to be read together with a bound on
`x`, which is how the explicit answers in `RequestProject/Answers.lean` are stated.
-/
namespace CubicFraction
/-- The numerator of the fraction under consideration. -/
def P (n : ℤ) : ℤ := 36 * n ^ 3 + 54 * n ^ 2 + 27 * n + 4
lemma two_mul_P (n : ℤ) : 2 * P n = 9 * (2 * n + 1) ^ 3 - 1 := by
  unfold P; ring
lemma P_sub (a b : ℤ) :
    P a - P b = (a - b) * (36 * (a ^ 2 + a * b + b ^ 2) + 54 * (a + b) + 27) := by
  unfold P; ring
/-- `P n` is never zero. -/
lemma P_ne_zero (n : ℤ) : P n ≠ 0 := by
  intro h
  have h2 : (9 : ℤ) * (2 * n + 1) ^ 3 - 1 = 0 := by rw [← two_mul_P, h]; ring
  have h9 : (9 : ℤ) ∣ 1 := ⟨(2 * n + 1) ^ 3, by linarith⟩
  norm_num at h9
/-- If `n₁ ≡ n₂` modulo `m`, then `P n₁ ≡ P n₂` modulo `m`. -/
lemma P_modEq {m n₁ n₂ : ℤ} (h : n₁ ≡ n₂ [ZMOD m]) : P n₁ ≡ P n₂ [ZMOD m] := by
  have hd : m ∣ n₁ - n₂ := Int.ModEq.dvd h.symm
  have h2 : m ∣ P n₁ - P n₂ := by
    rw [P_sub]; exact hd.mul_right _
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h2))
/-- No condition of the shape `x ≡ a₁ (mod b₁)`, taken over *all* `x` in that residue
class, can force the fraction `P n / x` to be an integer: the class always contains a
positive integer larger than `|P n|`, which cannot divide the nonzero number `P n`. -/
theorem not_forall_dvd_of_modEq (a₁ b₁ n : ℤ) (hb : 0 < b₁) :
    ∃ x : ℤ, 0 < x ∧ x ≡ a₁ [ZMOD b₁] ∧ ¬ x ∣ P n := by
  refine ⟨a₁ + b₁ * (|a₁| + |P n| + 1), ?_, ?_, ?_⟩
  · have h1 : |a₁| + |P n| + 1 ≤ b₁ * (|a₁| + |P n| + 1) := by
      nlinarith [abs_nonneg a₁, abs_nonneg (P n)]
    have h2 : -|a₁| ≤ a₁ := neg_abs_le a₁
    have h3 : 0 ≤ |P n| := abs_nonneg (P n)
    linarith
  · exact Int.modEq_iff_dvd.mpr ⟨-(|a₁| + |P n| + 1), by ring⟩
  · intro hdvd
    have hP : P n ≠ 0 := P_ne_zero n
    have habs : |P n| ≠ 0 := abs_ne_zero.mpr hP
    have hpos : 0 < |P n| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm habs)
    have hle : a₁ + b₁ * (|a₁| + |P n| + 1) ≤ |P n| :=
      Int.le_of_dvd hpos ((dvd_abs _ _).mpr hdvd)
    have h1 : |a₁| + |P n| + 1 ≤ b₁ * (|a₁| + |P n| + 1) := by
      nlinarith [abs_nonneg a₁, abs_nonneg (P n)]
    have h2 : -|a₁| ≤ a₁ := neg_abs_le a₁
    linarith
section Pow5
variable {k : ℕ}
instance neZero_pow5 (k : ℕ) : NeZero (5 ^ k) := ⟨by positivity⟩
/-- Cubing is injective on the units of `ZMod (5^k)`. -/
lemma cube_inj_pow5 (hk : 0 < k) {a b : ZMod (5 ^ k)}
    (ha : IsUnit a) (hb : IsUnit b) (h : a ^ 3 = b ^ 3) : a = b := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  have hAB : A ^ 3 = B ^ 3 := by ext; push_cast; exact h
  set U : (ZMod (5 ^ k))ˣ := A * B⁻¹ with hU
  have hU3 : U ^ 3 = 1 := by
    rw [hU, mul_pow, hAB, ← mul_pow, mul_inv_cancel, one_pow]
  have h3 : orderOf U ∣ 3 := orderOf_dvd_of_pow_eq_one hU3
  have htot : orderOf U ∣ Nat.totient (5 ^ k) := orderOf_dvd_of_pow_eq_one (ZMod.pow_totient U)
  have hcop : Nat.gcd 3 (Nat.totient (5 ^ k)) = 1 := by
    rw [Nat.totient_prime_pow (by norm_num) hk]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) (by norm_num)
  have h1 : orderOf U ∣ 1 := hcop ▸ Nat.dvd_gcd h3 htot
  have hU1 : U = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hAB' : A = B := by
    have := congrArg (fun u => u * B) hU1
    simpa [hU, mul_assoc] using this
  rw [hAB']
/-- Two integers whose `P`-values are divisible by `5^k` are congruent modulo `5^k`. -/
theorem pow5_dvd_P_unique (hk : 0 < k) {n₁ n₂ : ℤ}
    (h₁ : ((5 ^ k : ℕ) : ℤ) ∣ P n₁) (h₂ : ((5 ^ k : ℕ) : ℤ) ∣ P n₂) :
    n₁ ≡ n₂ [ZMOD ((5 ^ k : ℕ) : ℤ)] := by
  have hu9 : IsUnit (9 : ZMod (5 ^ k)) := by
    have h : ((9 : ℕ) : ZMod (5 ^ k)) = (9 : ZMod (5 ^ k)) := by push_cast; ring
    rw [← h, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hu2 : IsUnit (2 : ZMod (5 ^ k)) := by
    have h : ((2 : ℕ) : ZMod (5 ^ k)) = (2 : ZMod (5 ^ k)) := by push_cast; ring
    rw [← h, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have key : ∀ n : ℤ, ((5 ^ k : ℕ) : ℤ) ∣ P n →
      (9 : ZMod (5 ^ k)) * (2 * (n : ZMod (5 ^ k)) + 1) ^ 3 = 1 := by
    intro n hn
    have h0 : ((P n : ℤ) : ZMod (5 ^ k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hn)
    have hcast : ((2 * P n : ℤ) : ZMod (5 ^ k)) = ((9 * (2 * n + 1) ^ 3 - 1 : ℤ) : ZMod (5 ^ k)) := by
      rw [two_mul_P]
    push_cast at hcast
    rw [h0] at hcast
    linear_combination -hcast
  have k₁ := key n₁ h₁
  have k₂ := key n₂ h₂
  have hcube : (2 * (n₁ : ZMod (5 ^ k)) + 1) ^ 3 = (2 * (n₂ : ZMod (5 ^ k)) + 1) ^ 3 :=
    hu9.mul_left_cancel (by rw [k₁, k₂])
  have hunit : ∀ n : ℤ, (9 : ZMod (5 ^ k)) * (2 * (n : ZMod (5 ^ k)) + 1) ^ 3 = 1 →
      IsUnit (2 * (n : ZMod (5 ^ k)) + 1) := fun n hn =>
    IsUnit.of_mul_eq_one (b := 9 * (2 * (n : ZMod (5 ^ k)) + 1) ^ 2) (by linear_combination hn)
  have hm : (2 * (n₁ : ZMod (5 ^ k)) + 1) = (2 * (n₂ : ZMod (5 ^ k)) + 1) :=
    cube_inj_pow5 hk (hunit n₁ k₁) (hunit n₂ k₂) hcube
  have hn : ((n₁ : ℤ) : ZMod (5 ^ k)) = ((n₂ : ℤ) : ZMod (5 ^ k)) :=
    hu2.mul_left_cancel (by linear_combination hm)
  exact_mod_cast (ZMod.intCast_eq_intCast_iff n₁ n₂ (5 ^ k)).mp hn
/-- Characterisation of divisibility of `P n` by `5^k`: given one solution `a`, the
solutions are exactly the integers congruent to `a` modulo `5^k`. -/
theorem pow5_char (hk : 0 < k) {a : ℤ} (ha : ((5 ^ k : ℕ) : ℤ) ∣ P a) (n : ℤ) :
    ((5 ^ k : ℕ) : ℤ) ∣ P n ↔ n ≡ a [ZMOD ((5 ^ k : ℕ) : ℤ)] := by
  constructor
  · intro h
    exact pow5_dvd_P_unique hk h ha
  · intro h
    have hd : ((5 ^ k : ℕ) : ℤ) ∣ P n - P a := Int.ModEq.dvd (P_modEq h).symm
    simpa using dvd_add hd ha
/-- `P n` is even exactly when `n` is even (indeed `P n = 2 * (18n³+27n²+13n+2) + n`). -/
lemma two_dvd_P_iff (n : ℤ) : (2 : ℤ) ∣ P n ↔ (2 : ℤ) ∣ n := by
  have e : P n - 2 * (18 * n ^ 3 + 27 * n ^ 2 + 13 * n + 2) = n := by unfold P; ring
  constructor
  · intro h
    have h2 : (2 : ℤ) ∣ P n - 2 * (18 * n ^ 3 + 27 * n ^ 2 + 13 * n + 2) :=
      h.sub (Dvd.intro _ rfl)
    rwa [e] at h2
  · intro h
    have h2 : (2 : ℤ) ∣ n + 2 * (18 * n ^ 3 + 27 * n ^ 2 + 13 * n + 2) :=
      h.add (Dvd.intro _ rfl)
    have e' : n + 2 * (18 * n ^ 3 + 27 * n ^ 2 + 13 * n + 2) = P n := by unfold P; ring
    rwa [e'] at h2
/-- Characterisation of divisibility of `P n` by `2 * 5^k`: given one solution `a`, the
solutions are exactly the integers congruent to `a` modulo `2 * 5^k`. -/
theorem two_pow5_char (hk : 0 < k) {a : ℤ} (ha : (2 * (5 : ℤ) ^ k) ∣ P a) (n : ℤ) :
    (2 * (5 : ℤ) ^ k) ∣ P n ↔ n ≡ a [ZMOD 2 * (5 : ℤ) ^ k] := by
  have hcast : ((5 ^ k : ℕ) : ℤ) = (5 : ℤ) ^ k := by push_cast; ring
  have hcop : IsCoprime (2 : ℤ) ((5 : ℤ) ^ k) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).pow_right
  constructor
  · intro h
    have h5n : ((5 ^ k : ℕ) : ℤ) ∣ P n := by
      rw [hcast]; exact dvd_trans (dvd_mul_left _ 2) h
    have h5a : ((5 ^ k : ℕ) : ℤ) ∣ P a := by
      rw [hcast]; exact dvd_trans (dvd_mul_left _ 2) ha
    have h2n : (2 : ℤ) ∣ n := (two_dvd_P_iff n).mp (dvd_trans (dvd_mul_right 2 _) h)
    have h2a : (2 : ℤ) ∣ a := (two_dvd_P_iff a).mp (dvd_trans (dvd_mul_right 2 _) ha)
    have h5 : ((5 ^ k : ℕ) : ℤ) ∣ a - n :=
      Int.ModEq.dvd (pow5_dvd_P_unique hk h5n h5a)
    have h2 : (2 : ℤ) ∣ a - n := h2a.sub h2n
    rw [hcast] at h5
    exact Int.modEq_iff_dvd.mpr (hcop.mul_dvd h2 h5)
  · intro h
    have hd : (2 * (5 : ℤ) ^ k) ∣ P n - P a := Int.ModEq.dvd (P_modEq h).symm
    simpa using dvd_add hd ha
end Pow5
end CubicFraction
