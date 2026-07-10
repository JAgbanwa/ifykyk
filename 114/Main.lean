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
set_option grind.warning false
/-!
# Large Modular Congruences for which `x ∣ 36 n³ − 19`
This file formalises the paper *"Large Modular Congruences for which `x ∣ 36 n³ − 19`:
A CRT / cube-root construction with 30- and 40-digit moduli"*.
The mathematical content is:
* **Lemma 1.** For a prime `p ≡ 2 (mod 3)` the map `t ↦ t³` is a bijection of `ZMod p`
  (`LargeCongruences.cube_bijective`); consequently every element has a unique cube root
  (`LargeCongruences.exists_cube_root`).
* **Construction 1.** For a prime `p ≡ 2 (mod 3)`, `p ≠ 2`, there is a residue `a` with
  `36 a³ ≡ 19 (mod p)` (`LargeCongruences.exists_root_zmod`), and hence a whole congruence
  class `n ≡ a (mod p)` on which `p ∣ 36 n³ − 19` (`LargeCongruences.key_single`).
* **Theorem 1 (multi-prime CRT combination).** For a finite set of distinct primes each
  `≡ 2 (mod 3)` and `≠ 2`, with product `M`, there is a residue `A` such that
  `M ∣ 36 n³ − 19` for every `n ≡ A (mod M)` (`LargeCongruences.multiprime`).
* **Numerical instances (§4–§7).** The four explicit instances from the paper (two/three
  primes of 30/40 digits) are verified directly by exact integer arithmetic:
  the root identities `36 aᵢ³ ≡ 19 (mod pᵢ)`, the product `M = ∏ pᵢ`, the exact division
  `36 A³ − 19 = M · Q`, and the resulting infinite family `M ∣ 36 n³ − 19` for `n ≡ A (mod M)`.
Primality of the 30- and 40-digit `pᵢ` (checked in the paper by an external arbitrary-precision
library) is *not* re-verified here: certifying primality of such numbers inside Lean is
computationally expensive and, crucially, is not needed for the family statements, which follow
from the exact divisibility `M ∣ 36 A³ − 19` alone.
-/
namespace LargeCongruences
/-! ## Lemma 1: cubing is a bijection modulo a prime `p ≡ 2 (mod 3)` -/
/-
**Lemma 1.** If `p` is a prime with `p ≡ 2 (mod 3)`, then `t ↦ t³` is a bijection of
`ZMod p`.
-/
lemma cube_bijective (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun t : ZMod p => t ^ 3) := by
  -- Since `ZMod p` is finite, a self-map is bijective iff injective. Reduce to injectivity of `t ↦ t^3`.
  have h_inj : Function.Injective (fun t : (ZMod p) => t ^ 3) := by
    -- If `x ≠ 0` then `y ≠ 0`, so both are units; use injectivity of cubing on units (from the bijection) to conclude `x = y`.
    have h_unit : ∀ x : ZMod p, x ≠ 0 → ∀ y : ZMod p, y ≠ 0 → x^3 = y^3 → x = y := by
      -- Since $p \equiv 2 \pmod{3}$, we have that $x^{p-1} \equiv 1 \pmod{p}$ for any $x \neq 0$.
      have h_order : ∀ x : ZMod p, x ≠ 0 → x ^ (p - 1) = 1 := by
        exact fun x hx => ZMod.pow_card_sub_one_eq_one hx;
      -- Since $p \equiv 2 \pmod{3}$, we have that $x^{(2p-1)/3} = y^{(2p-1)/3}$ implies $x = y$.
      intros x hx y hy hxy
      have h_eq : x ^ (2 * p - 1) = y ^ (2 * p - 1) := by
        rw [ show 2 * p - 1 = 3 * ( ( 2 * p - 1 ) / 3 ) by omega, pow_mul, pow_mul, hxy ];
      convert h_eq using 1 <;> rw [ show 2 * p - 1 = ( p - 1 ) + p by omega, pow_add ] <;> simp +decide [ * ];
    intro x y; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide ;
    · exact fun h => absurd h.symm ( pow_ne_zero 3 hy );
    · exact h_unit x hx y hy;
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩
/-
Consequently every element of `ZMod p` has a cube root.
-/
lemma exists_cube_root (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (c : ZMod p) :
    ∃ a : ZMod p, a ^ 3 = c := by
  convert ( cube_bijective p hp |> Function.Bijective.surjective ) c
/-! ## Construction 1: a residue solving `36 a³ ≡ 19 (mod p)` -/
/-
`36` is a unit in `ZMod p` when `p ≠ 2` and `p ≡ 2 (mod 3)` (so `p ≠ 3`).
-/
lemma isUnit_thirtysix (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (h2 : p ≠ 2) :
    IsUnit (36 : ZMod p) := by
  convert isUnit_iff_ne_zero.mpr _;
  erw [ Ne, ZMod.natCast_eq_zero_iff ] ; intro H; have := Nat.le_of_dvd ( by decide ) H; interval_cases p <;> trivial;
/-
**Construction 1 (residue form).** For a prime `p ≡ 2 (mod 3)`, `p ≠ 2`, there is a residue
`a ∈ ZMod p` with `36 a³ = 19`.
-/
lemma exists_root_zmod (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (h2 : p ≠ 2) :
    ∃ a : ZMod p, 36 * a ^ 3 = 19 := by
  -- By `isUnit_thirtysix p hp h2`, `(36 : ZMod p)` is a unit, so it has an inverse and `36 * (19 * 36⁻¹) = 19` (in the field `ZMod p`; use `mul_inv_cancel₀` since `36 ≠ 0`).
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, 36 * c = 19 := by
    exact ⟨ 19 / 36, mul_div_cancel₀ _ <| by have := isUnit_thirtysix p ( hp ) h2; simpa using this.ne_zero ⟩;
  obtain ⟨ a, ha ⟩ := exists_cube_root p hp c; use a; aesop;
/-
**Construction 1 (integer / congruence-class form).** For a prime `p ≡ 2 (mod 3)`, `p ≠ 2`,
there is an integer `a` such that `p ∣ 36 n³ − 19` for every `n ≡ a (mod p)`.
-/
theorem key_single (p : ℕ) (hp : p.Prime) (h3 : p % 3 = 2) (h2 : p ≠ 2) :
    ∃ a : ℤ, ∀ n : ℤ, n ≡ a [ZMOD (p : ℤ)] → (p : ℤ) ∣ 36 * n ^ 3 - 19 := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod p, 36 * a ^ 3 = 19 := by
    haveI := Fact.mk hp; exact exists_root_zmod p h3 h2;
  use a.val;
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ] ;
/-! ## A generic "whole class" divisibility lemma
If `M ∣ 36 A³ − 19` then `M ∣ 36 n³ − 19` for every `n ≡ A (mod M)`.  This is the elementary
step that upgrades a single verified representative to an entire congruence class, and it is what
makes the numerical instances below infinite families rather than single checked integers. -/
/-
If `M` divides `36 A³ − 19`, it divides `36 n³ − 19` for every `n ≡ A (mod M)`.
-/
lemma class_dvd (M A : ℤ) (h : M ∣ 36 * A ^ 3 - 19) :
    ∀ n : ℤ, n ≡ A [ZMOD M] → M ∣ 36 * n ^ 3 - 19 := by
  intro n hn
  have hd : M ∣ n - A := hn.symm.dvd
  have hid : 36 * n ^ 3 - 19
      = (36 * A ^ 3 - 19) + (n - A) * (36 * (n ^ 2 + n * A + A ^ 2)) := by ring
  rw [hid]
  exact dvd_add h (hd.mul_right _)
/-! ## Theorem 1: multi-prime CRT combination -/
/-
Auxiliary: a prime `p` not in a finite set `s` of primes is coprime (over `ℤ`) to the product
of the primes in `s`.
-/
lemma coprime_prime_prod (p : ℕ) (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hps : p ∉ s) :
    IsCoprime (p : ℤ) (∏ q ∈ s, (q : ℤ)) := by
  exact IsCoprime.prod_right fun q hq => by have := Nat.coprime_primes hp ( hs q hq ) ; aesop;
/-
**Theorem 1.** Let `s` be a finite set of distinct primes, each `≡ 2 (mod 3)` and `≠ 2`, and
let `M = ∏ p ∈ s, p`.  Then there is an integer `A` such that `M ∣ 36 n³ − 19` for every
`n ≡ A (mod M)`.  Since `M` and `A` can be made arbitrarily large by taking more/larger primes,
this exhibits arbitrarily large moduli `M` exactly dividing `36 n³ − 19` on an entire residue
class.
-/
theorem multiprime (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p % 3 = 2 ∧ p ≠ 2) :
    ∃ A : ℤ, ∀ n : ℤ, n ≡ A [ZMOD ((∏ p ∈ s, p : ℕ) : ℤ)] →
      ((∏ p ∈ s, p : ℕ) : ℤ) ∣ 36 * n ^ 3 - 19 := by
  induction' s using Finset.induction with q t hq htail;
  · exact ⟨ 0, fun n hn => one_dvd _ ⟩;
  · obtain ⟨A', hA'⟩ := htail (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    obtain ⟨a, ha⟩ := key_single q (hs q (Finset.mem_insert_self q t)).left (hs q (Finset.mem_insert_self q t)).right.left (hs q (Finset.mem_insert_self q t)).right.right;
    -- By the Chinese Remainder Theorem, there exists an integer $A$ such that $A \equiv A' \pmod{M'}$ and $A \equiv a \pmod{q}$.
    obtain ⟨A, hA⟩ : ∃ A : ℤ, A ≡ A' [ZMOD (∏ p ∈ t, p : ℤ)] ∧ A ≡ a [ZMOD q] := by
      have h_coprime : IsCoprime (∏ p ∈ t, (p : ℤ)) (q : ℤ) := by
        exact IsCoprime.prod_left fun p hp => by have := Nat.coprime_primes ( hs p ( Finset.mem_insert_of_mem hp ) |>.1 ) ( hs q ( Finset.mem_insert_self q t ) |>.1 ) ; aesop;
      rcases h_coprime with ⟨ u, v, h ⟩;
      use A' + u * (∏ p ∈ t, (p : ℤ)) * (a - A');
      norm_num [ Int.modEq_iff_dvd ];
      exact ⟨ dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _, ⟨ v * ( a - A' ), by linear_combination -h * ( a - A' ) ⟩ ⟩;
    use A; intro n hn; simp_all +decide [ Finset.prod_insert hq ] ;
    refine' IsCoprime.mul_dvd _ _ _;
    · exact IsCoprime.prod_right fun x hx => by have := Nat.coprime_primes hs.1.1 ( hs.2 x hx |>.1 ) ; aesop;
    · exact ha n ( hn.of_dvd ( dvd_mul_right _ _ ) |> Int.ModEq.trans <| hA.2 );
    · exact hA' n ( hn.of_dvd ( dvd_mul_left _ _ ) |> Int.ModEq.trans <| hA.1 )
/-! ## §4 Two 30-digit primes (k = 2) -/
/-
**§4.** The two 30-digit primes and their cube-roots, the 60-digit modulus `M = p₁p₂`, the
59-digit representative `A`, and the 119-digit quotient `Q` with `36 A³ − 19 = M · Q`.  All of the
root identities, the product identity, the exact division, and the resulting infinite family
`M ∣ 36 n³ − 19` for `n ≡ A (mod M)` are verified by exact integer arithmetic.
-/
theorem instance_k2_30digit :
    let p₁ : ℤ := 432256083118531044858259323599
    let a₁ : ℤ := 205375962562755822717169031496
    let p₂ : ℤ := 508951041752918591462038694231
    let a₂ : ℤ := 11998528096759146724786261916
    let M : ℤ := 219997183807212542923931096695598007560918353360263243457369
    let A : ℤ := 61583691402182783047260797510703276439292047987969866884962
    let Q : ℤ := 38219282687467843755039989619336413202799418213239056237824742757700405657626958942597846112998216708072139112513223381
    p₁ ∣ 36 * a₁ ^ 3 - 19 ∧ p₂ ∣ 36 * a₂ ^ 3 - 19 ∧ M = p₁ * p₂ ∧
      36 * A ^ 3 - 19 = M * Q ∧ (∀ n : ℤ, n ≡ A [ZMOD M] → M ∣ 36 * n ^ 3 - 19) := by
  exact ⟨ by native_decide, by native_decide, by native_decide, by native_decide, fun n hn => class_dvd _ _ ( by native_decide ) n hn ⟩
/-! ## §5 Three 30-digit primes (k = 3) -/
/-
**§5.** Three fresh 30-digit primes, the 90-digit modulus `M = p₁p₂p₃`, the 90-digit
representative `A`, and the 180-digit quotient `Q` with `36 A³ − 19 = M · Q`.
-/
theorem instance_k3_30digit :
    let p₁ : ℤ := 779282871203804318581334453057
    let a₁ : ℤ := 540863547358444129637446662643
    let p₂ : ℤ := 917485502986111972709840010173
    let a₂ : ℤ := 765515263147582646243402496698
    let p₃ : ℤ := 422843868764454355911216773723
    let a₃ : ℤ := 173885648024960625137792429386
    let M : ℤ := 302325220948348183420434660024015348902086281522777512680498475446030651529604772341579503
    let A : ℤ := 182470001039324181181024873011044406335174068803296028244172097475931272694261226503431598
    let Q : ℤ := 723440045918937868278733134032344285097446574084321029094017717823428606222435878944285733479052368954298584972235671037551447033227302246880204085670050855668916609015702186192131
    p₁ ∣ 36 * a₁ ^ 3 - 19 ∧ p₂ ∣ 36 * a₂ ^ 3 - 19 ∧ p₃ ∣ 36 * a₃ ^ 3 - 19 ∧
      M = p₁ * p₂ * p₃ ∧ 36 * A ^ 3 - 19 = M * Q ∧
      (∀ n : ℤ, n ≡ A [ZMOD M] → M ∣ 36 * n ^ 3 - 19) := by
  refine' ⟨ by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, _ ⟩;
  exact fun n hn => class_dvd _ _ ( by native_decide ) n hn
/-! ## §6 Two 40-digit primes (k = 2) -/
/-
**§6.** Two 40-digit primes, the 80-digit modulus `M = p₁p₂`, the 80-digit representative `A`,
and the 160-digit quotient `Q` with `36 A³ − 19 = M · Q`.
-/
theorem instance_k2_40digit :
    let p₁ : ℤ := 7729484335457653901640057298531371241781
    let a₁ : ℤ := 7668575607239450973459863267707132263860
    let p₂ : ℤ := 2486598372481845396683104279916570951657
    let a₂ : ℤ := 609530524018264138310326718615033307496
    let M : ℤ := 19220123168672920512532048525080739795893456098633704192461052168447373009581117
    let A : ℤ := 12055573306960757229878249326862599227290509643013675419894826308035075337947215
    let Q : ℤ := 3281783589609439060274407871106333299264698047304666391611865457187494168830153506599538715008344851754116620345469289412464296994115391491979199807003772632893
    p₁ ∣ 36 * a₁ ^ 3 - 19 ∧ p₂ ∣ 36 * a₂ ^ 3 - 19 ∧ M = p₁ * p₂ ∧
      36 * A ^ 3 - 19 = M * Q ∧ (∀ n : ℤ, n ≡ A [ZMOD M] → M ∣ 36 * n ^ 3 - 19) := by
  refine' ⟨ by native_decide, by native_decide, by native_decide, by native_decide, _ ⟩;
  intro n hn; exact class_dvd _ _ ( by native_decide ) _ hn;
/-! ## §7 Three 40-digit primes (k = 3) — the largest instance -/
/-
**§7.** Three 40-digit primes, the 120-digit modulus `M = p₁p₂p₃`, the 119-digit
representative `A`, and the 240-digit quotient `Q` with `36 A³ − 19 = M · Q`.  This is the largest
instance in the paper.
-/
theorem instance_k3_40digit :
    let p₁ : ℤ := 6719198563363963000306859976745602011477
    let a₁ : ℤ := 3490701603819271511450476386979369043828
    let p₂ : ℤ := 5014753468477740779475587342292599756573
    let a₂ : ℤ := 2189794512725854244347716309834217468129
    let p₃ : ℤ := 4350736286376564530047381650448847768399
    let a₃ : ℤ := 525176878515189528938215354529508172272
    let M : ℤ := 146598599970416865193503095382122376155797697327993857757772703444309911094348084964151091360030057229085267028040668079
    let A : ℤ := 78645806109075982274155955035418384113009237358084530484254201316396650239497999707497613326168293812811504563595780749
    let Q : ℤ := 119453638517902053794963958283357629777707983376380601474787235288607383318513130562995313813671450899537612665803296173072136255334374568105736108037208680482571587733372866341630091424872047846333343491478053473403358730772112480717305455
    p₁ ∣ 36 * a₁ ^ 3 - 19 ∧ p₂ ∣ 36 * a₂ ^ 3 - 19 ∧ p₃ ∣ 36 * a₃ ^ 3 - 19 ∧
      M = p₁ * p₂ * p₃ ∧ 36 * A ^ 3 - 19 = M * Q ∧
      (∀ n : ℤ, n ≡ A [ZMOD M] → M ∣ 36 * n ^ 3 - 19) := by
  refine' ⟨ by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, _ ⟩;
  intro n hn; rw [ Int.dvd_iff_emod_eq_zero ] ; norm_num [ Int.sub_emod, Int.mul_emod, pow_succ, hn.eq ] ;
end LargeCongruences
