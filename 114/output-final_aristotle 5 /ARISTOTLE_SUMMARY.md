# Summary of changes for run 73f8e991-be32-489e-97a5-358e45b74d24
I regenerated all ten sets of congruences so that the four constants are now **pairwise distinct** — in particular `a₁ ≠ a₂` and `a₁ ≠ b₂`, as you asked (previously `a₁ = b₂`).
**New construction.** For each digit size `d = 10, 20, …, 100`:
- `a₁ = p`, a `d`-digit prime with `p ≡ 2 (mod 3)` and `2p < 10^d`;
- `b₁ = 10^d − 1`, so `k ≡ a₁ (mod b₁)` with `0 < k < b₁` pins `k = p`;
- `b₂ = 2p` (a multiple of `p`, hence `b₂ ≠ a₁`);
- `a₂` = the residue in the open interval `(p, 2p)` with `350892·a₂³ ≡ 1 (mod p)`, hence `a₂ ≠ a₁` and `a₂ ≠ b₂`.
Since `p ∣ b₂`, every `m ≡ a₂ (mod b₂)` satisfies `m ≡ a₂ (mod p)`, so `p ∣ 350892·m³ − 1`, i.e. `(350892 m³ − 1)/k` is an integer. The `m`-congruence carries no side conditions.
Example (10 digits): `a₁ = 1000000007`, `b₁ = 9999999999`, `a₂ = 1600805382`, `b₂ = 2000000014` — four distinct 10-digit numbers.
**What is machine-checked** in `RequestProject/CubicCongruence.lean` (builds cleanly, no `sorry`, only the standard axioms):
- `CubicCongruence.integrality_digits_d` for `d = 10, …, 100`: the integrality statement above, with explicit certified quotients;
- `CubicCongruence.constants_distinct_d` for each `d`: the four constants are pairwise distinct (proved by `decide`);
- `CubicCongruence.no_unbounded_k_congruence` (unchanged): the bounds `0 < k < b₁` cannot be removed — no pair of congruences can force divisibility for *every* `k` in an infinite residue class, since `350892 m³ − 1` has only finitely many divisors.
The full constant list is in `ANSWERS.md`, updated to the new values.
# Summary of changes for run 83c85c99-43af-41dc-aec1-40f25bb774ee
**What I built.** `RequestProject/CubicCongruence.lean` (builds cleanly, no `sorry`, only the standard axioms) contains ten machine-checked theorems `CubicCongruence.integrality_digits_d` for d = 10, 20, …, 100. Each one states:
> if `k ≡ a₁ (mod b₁)` with `0 < k < b₁`, and `m ≡ a₂ (mod b₂)`, then `k ∣ 350892·m³ − 1`, i.e. `(350892·m³ − 1)/k` is an integer,
with all four constants `a₁, b₁, a₂, b₂` having exactly d digits. The full list of constants is in `ANSWERS.md`; the 10-digit case is `a₁ = 9999999929`, `b₁ = 9999999999`, `a₂ = 7889599099`, `b₂ = 9999999929`.
**How the constants were chosen.** For each d, `b₁ = 10^d − 1`, and `a₁ = b₂ = p` is a d-digit prime with `p ≡ 2 (mod 3)`, so cubing is a bijection mod `p` and the congruence `350892·x³ ≡ 1 (mod p)` has a unique solution `a₂` (checked to be d digits). Then every integer `m ≡ a₂ (mod p)` satisfies `p ∣ 350892·m³ − 1`; the `m`-congruence carries no side conditions.
**An important caveat, also proved.** The bounds `0 < k < b₁` (which pin `k` down to `a₁` inside its residue class) cannot be removed. The theorem `CubicCongruence.no_unbounded_k_congruence` proves that for *any* choice of `a₁, b₁, a₂, b₂`, it is false that all `k ≡ a₁ (mod b₁)` and all `m ≡ a₂ (mod b₂)` give integrality — because `350892·m³ − 1` is a fixed nonzero integer with finitely many divisors, while a residue class contains arbitrarily large `k`. So a purely unrestricted congruence condition on `k` is impossible, and the formulation above is the correct one.
A shared helper lemma `CubicCongruence.dvd_of_emod` transfers the divisibility from the residue `a₂` to every `m` in its class; the ten instances then discharge the explicit large-number divisibility `p ∣ 350892·a₂³ − 1` with certified quotients.
