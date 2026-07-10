import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-!
# Congruence Conditions for the Square Constraint in `y² = (6n + x)² + (36n³ − 19)/x`
This file formalises the main results of the note *"Congruence Conditions for the Square
Constraint in `y² = (6n + x)² + (36n³ − 19)/x`"*.
We encode a solution `(n, x, y)` of
  `x ∣ 36 n³ − 19`  and  `y² = (6n + x)² + (36 n³ − 19)/x`
by the equivalent division-free statement `x ≠ 0 ∧ x * (y² − (6n + x)²) = 36 n³ − 19`.
Indeed, from the latter, `x ∣ 36 n³ − 19` is automatic and the quotient is `y² − (6n + x)²`.
The two main theorems are:
* `SquareSolution.forced_congruences` (Lemma 1): any solution satisfies
  `n ≡ 0 (mod 3)`, `x ≡ 7 (mod 12)` and `y ≡ 0 (mod 6)`.
* `squareSolution_iff_sum_three_cubes_114` (Theorem 1): a solution exists **iff** `114`
  is a sum of three integer cubes.  (The latter is an open problem, so this is an
  equivalence, not an existence statement.)
-/
namespace CongruenceSquare114
/-- A triple `(n, x, y)` is a *square solution* of the constraint if `x ≠ 0` and
`x * (y² − (6n + x)²) = 36 n³ − 19`.  This is equivalent to `x ∣ 36 n³ − 19` together with
`y² = (6n + x)² + (36 n³ − 19)/x`. -/
def SquareSolution (n x y : ℤ) : Prop :=
  x ≠ 0 ∧ x * (y ^ 2 - (6 * n + x) ^ 2) = 36 * n ^ 3 - 19
/-
The equivalent formulation with explicit divisibility and quotient.
-/
theorem squareSolution_iff_div (n x y : ℤ) :
    SquareSolution n x y ↔
      (x ≠ 0 ∧ x ∣ (36 * n ^ 3 - 19) ∧ y ^ 2 = (6 * n + x) ^ 2 + (36 * n ^ 3 - 19) / x) := by
  constructor <;> intro h;
  · exact ⟨ h.1, ⟨ _, h.2.symm ⟩, by rw [ ← h.2, Int.mul_ediv_cancel_left _ h.1 ] ; ring ⟩;
  · exact ⟨ h.1, by cases lt_or_gt_of_ne h.1 <;> nlinarith [ Int.ediv_mul_cancel h.2.1 ] ⟩
/-
**Lemma 1 (Basic local restrictions).**  Any square solution `(n, x, y)` satisfies
`n ≡ 0 (mod 3)`, `x ≡ 7 (mod 12)` and `y ≡ 0 (mod 6)`.
-/
theorem SquareSolution.forced_congruences {n x y : ℤ} (h : SquareSolution n x y) :
    n % 3 = 0 ∧ x % 12 = 7 ∧ y % 6 = 0 := by
  obtain ⟨ hx₁, hx₂ ⟩ := h;
  -- From x*(y^2 - (6n+x)^2) ≡ 2 (mod 3), we have x ≡ 1 (mod 3).
  have hx_mod3 : x % 3 = 1 := by
    have := congr_arg ( · % 3 ) hx₂; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ ] at this; ( have := Int.emod_nonneg x three_pos.ne'; ( have := Int.emod_nonneg y three_pos.ne'; ( have := Int.emod_lt_of_pos x three_pos; ( have := Int.emod_lt_of_pos y three_pos; interval_cases x % 3 <;> interval_cases y % 3 <;> trivial; ) ) ) );
  -- From x*(y^2 - (6n+x)^2) ≡ 1 (mod 4), we have x ≡ 3 (mod 4).
  have hx_mod4 : x % 4 = 3 := by
    have := congr_arg ( · % 4 ) hx₂; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, sq ] at this; have := Int.emod_nonneg x four_pos.ne'; have := Int.emod_nonneg y four_pos.ne'; have := Int.emod_lt_of_pos x four_pos; have := Int.emod_lt_of_pos y four_pos; interval_cases x % 4 <;> interval_cases y % 4 <;> norm_num at *;
    all_goals have := Int.emod_nonneg n four_pos.ne'; have := Int.emod_lt_of_pos n four_pos; interval_cases n % 4 <;> contradiction;
  -- From x*(y^2 - (6n+x)^2) ≡ -1 (mod 9), we have n ≡ 0 (mod 3).
  have hn_mod3 : n % 3 = 0 := by
    replace hx₂ := congr_arg ( · % 9 ) hx₂ ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ ] at hx₂ ⊢;
    rw [ Int.dvd_iff_emod_eq_zero ] ; rw [ ← Int.emod_emod_of_dvd n ( by decide : ( 3 : ℤ ) ∣ 9 ) ] ; have := Int.emod_nonneg n ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg x ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg y ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos n ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos x ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases n % 9 <;> interval_cases x % 9 <;> interval_cases y % 9 <;> simp +decide at hx₂ ⊢;
  -- From x*(y^2 - (6n+x)^2) ≡ -1 (mod 9), we have y ≡ 0 (mod 6).
  have hy_mod6 : y % 6 = 0 := by
    replace hx₂ := congr_arg ( · % 6 ) hx₂ ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, hn_mod3, hx_mod3, hx_mod4 ] at hx₂ ⊢;
    rw [ Int.dvd_iff_emod_eq_zero ] ; rw [ ← Int.emod_emod_of_dvd x ( by decide : ( 3 : ℤ ) ∣ 6 ), ← Int.emod_emod_of_dvd x ( by decide : ( 4 : ℤ ) ∣ 12 ) ] at *; have := Int.emod_nonneg x ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg y ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos x ( by decide : ( 6 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 6 : ℤ ) > 0 ) ; interval_cases x % 6 <;> interval_cases y % 6 <;> trivial;
  exact ⟨hn_mod3, by omega, hy_mod6⟩
/-
No integer cube equals `114` (since `4³ = 64 < 114 < 125 = 5³`).
-/
theorem no_int_cube_114 (t : ℤ) : t ^ 3 ≠ 114 := by
  exact ne_of_apply_ne ( fun x => x % 9 ) ( by norm_num [ pow_succ, Int.mul_emod ] ; have := Int.emod_nonneg t ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos t ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases t % 9 <;> trivial )
/-
If `U³ + V³ + W³ = 114`, then each of `U, V, W` is `≡ 2 (mod 3)`
(because cubes mod 9 are `0, ±1` and `114 ≡ −3 (mod 9)`).
-/
theorem sum_three_cubes_114_mod3 {U V W : ℤ} (h : U ^ 3 + V ^ 3 + W ^ 3 = 114) :
    U % 3 = 2 ∧ V % 3 = 2 ∧ W % 3 = 2 := by
  -- Reduce modulo 9. Cubes mod 9 are only 0, 1, 8 (i.e. 0, ±1). Since 114 ≡ 6 (mod 9), and each of U^3,V^3,W^3 is in {0,1,8} mod 9, the only way three such values sum to 6 mod 9 is 8+8+8.
  have h_mod9 : (U ^ 3 + V ^ 3 + W ^ 3) % 9 = 6 := by
    norm_num [ h ];
  norm_num [ pow_succ, Int.add_emod, Int.mul_emod ] at h_mod9;
  rw [ ← Int.emod_emod_of_dvd U ( by decide : ( 3 : ℤ ) ∣ 9 ), ← Int.emod_emod_of_dvd V ( by decide : ( 3 : ℤ ) ∣ 9 ), ← Int.emod_emod_of_dvd W ( by decide : ( 3 : ℤ ) ∣ 9 ) ] ; have := Int.emod_nonneg U ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg V ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg W ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos U ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos V ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos W ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases U % 9 <;> interval_cases V % 9 <;> interval_cases W % 9 <;> simp +decide at h_mod9 ⊢;
/-
If `U³ + V³ + W³ = 114`, then exactly one of `U, V, W` is even
(because `114 ≡ 2 (mod 8)` and `114` is even).
-/
theorem sum_three_cubes_114_one_even {U V W : ℤ} (h : U ^ 3 + V ^ 3 + W ^ 3 = 114) :
    (U % 2 = 0 ∧ V % 2 = 1 ∧ W % 2 = 1) ∨
    (V % 2 = 0 ∧ U % 2 = 1 ∧ W % 2 = 1) ∨
    (W % 2 = 0 ∧ U % 2 = 1 ∧ V % 2 = 1) := by
  cases Int.emod_two_eq_zero_or_one U <;> cases Int.emod_two_eq_zero_or_one V <;> cases Int.emod_two_eq_zero_or_one W <;> simp +decide only [*];
  · exact absurd ( congr_arg ( · % 8 ) h ) ( by rw [ ← Int.emod_add_mul_ediv U 2, ← Int.emod_add_mul_ediv V 2, ← Int.emod_add_mul_ediv W 2, ‹U % 2 = 0›, ‹V % 2 = 0›, ‹W % 2 = 0› ] ; ring_nf; norm_num [ Int.add_emod, Int.mul_emod ] );
  · exact absurd ( congr_arg ( · % 2 ) h ) ( by norm_num [ pow_succ, Int.add_emod, Int.mul_emod, ‹U % 2 = 0›, ‹V % 2 = 0›, ‹W % 2 = 1› ] );
  · replace h := congr_arg ( · % 4 ) h ; rcases Int.even_or_odd' U with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' V with ⟨ l, rfl | rfl ⟩ <;> rcases Int.even_or_odd' W with ⟨ m, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
    have := Int.emod_nonneg l four_pos.ne'; have := Int.emod_lt_of_pos l four_pos; interval_cases l % 4 <;> contradiction;
  · exact absurd ( congr_arg ( · % 2 ) h ) ( by norm_num [ pow_succ', Int.add_emod, Int.mul_emod, ‹U % 2 = _›, ‹V % 2 = _›, ‹W % 2 = _› ] );
  · exact absurd ( congr_arg ( · % 2 ) h ) ( by norm_num [ pow_succ, Int.add_emod, Int.mul_emod, ‹U % 2 = _›, ‹V % 2 = _›, ‹W % 2 = _› ] )
/-
Forward direction of Theorem 1: a square solution yields a representation of `114`
as a sum of three cubes, via `U = 6n + 2x`, `V = y − x`, `W = −y − x`.
-/
theorem SquareSolution.sum_three_cubes {n x y : ℤ} (h : SquareSolution n x y) :
    (6 * n + 2 * x) ^ 3 + (y - x) ^ 3 + (-y - x) ^ 3 = 114 := by
  linarith [ h.2 ]
/-
Reverse direction of Theorem 1, in the normalised case where `U` is the even variable:
from `U³ + V³ + W³ = 114` with `U` even and `V, W` odd, we obtain a square solution.
-/
theorem sum_three_cubes_114_to_solution {U V W : ℤ}
    (h : U ^ 3 + V ^ 3 + W ^ 3 = 114)
    (hU : U % 2 = 0) (hV : V % 2 = 1) (hW : W % 2 = 1) :
    SquareSolution ((U + V + W) / 6) (-((V + W) / 2)) ((V - W) / 2) := by
  constructor;
  · grind +suggestions;
  · -- By definition of $n$, $x$, and $y$, we know that $6n = U + V + W$, $2x = -(V + W)$, and $2y = V - W$.
    have hn : 6 * ((U + V + W) / 6) = U + V + W := by
      rw [ Int.mul_ediv_cancel' ];
      exact Int.dvd_of_emod_eq_zero ( by have := congr_arg ( · % 6 ) h; norm_num [ pow_succ, Int.add_emod, Int.mul_emod ] at this ⊢; have := Int.emod_nonneg U ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg V ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg W ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos U ( by decide : ( 6 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos V ( by decide : ( 6 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos W ( by decide : ( 6 : ℤ ) > 0 ) ; interval_cases U % 6 <;> interval_cases V % 6 <;> interval_cases W % 6 <;> trivial )
    have hx2 : 2 * (-((V + W) / 2)) = -(V + W) := by
      omega
    have hy2 : 2 * ((V - W) / 2) = V - W := by
      grind;
    grind
/-
**Theorem 1 (Equivalence with three cubes).**  A square solution exists if and only if
`114` is a sum of three integer cubes.
-/
theorem squareSolution_iff_sum_three_cubes_114 :
    (∃ n x y : ℤ, SquareSolution n x y) ↔
      (∃ U V W : ℤ, U ^ 3 + V ^ 3 + W ^ 3 = 114) := by
  constructor;
  · exact fun ⟨ n, x, y, h ⟩ => ⟨ 6 * n + 2 * x, y - x, -y - x, by linarith [ SquareSolution.sum_three_cubes h ] ⟩;
  · rintro ⟨ U, V, W, h ⟩;
    obtain ⟨hU, hV, hW⟩ : (U % 2 = 0 ∧ V % 2 = 1 ∧ W % 2 = 1) ∨ (V % 2 = 0 ∧ U % 2 = 1 ∧ W % 2 = 1) ∨ (W % 2 = 0 ∧ U % 2 = 1 ∧ V % 2 = 1) := by
      apply sum_three_cubes_114_one_even h;
    · exact ⟨ _, _, _, sum_three_cubes_114_to_solution h hU hV hW ⟩;
    · rcases ‹_› with ( ⟨ hV, hU, hW ⟩ | ⟨ hW, hU, hV ⟩ );
      · exact ⟨ ( V + U + W ) / 6, - ( ( U + W ) / 2 ), ( U - W ) / 2, sum_three_cubes_114_to_solution ( by linarith ) hV hU hW ⟩;
      · exact ⟨ ( W + U + V ) / 6, - ( ( U + V ) / 2 ), ( U - V ) / 2, sum_three_cubes_114_to_solution ( by linarith ) hW hU hV ⟩
end CongruenceSquare114
