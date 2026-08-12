# Summary of changes for run d35a9763-6ff4-42a4-9c57-6eccd2e7c1aa
Reworked the construction so that a₁ ≠ b₂ (indeed all four constants of each family are now pairwise distinct), and reproved everything in Lean.
**New construction.** For each digit size d ∈ {20, 40, 60, 80, 100}: a₁ = p (a prime with p ≡ 2 mod 3), b₁ = 2p, **b₂ = 3p**, and a₂ is a solution of 36·a₂³ ≡ 19 (mod p). Since n ≡ a₂ (mod 3p) implies n ≡ a₂ (mod p), the divisibility still holds, while a₁ = p is now different from b₂ = 3p. For d = 80 the previous prime was too large for 3p to stay at 80 digits, so a new 80-digit prime and matching a₂ were computed; the other four families keep their previous a₁, b₁, a₂ with the new b₂.
**What is proved in `RequestProject/Main.lean`** (builds cleanly, no `sorry`, only the standard axioms `propext`, `Classical.choice`, `Quot.sound`):
- `int_div_of_congruences` and the new variant `int_div_of_congruences_mul_three` — the general criterion, with the n-congruence taken modulo 3p.
- `fraction_integer_20/40/60/80/100` — for each family: x ≡ a₁ (mod b₁), 0 < x < b₁, n ≡ a₂ (mod b₂) ⟹ x ∣ 36n³ − 19, i.e. (36n³ − 19)/x is an integer.
- `digits_20/…/100` — each of the four constants has exactly d decimal digits.
- `distinct_20/…/100` — the four constants of each family are pairwise distinct, in particular a₁ ≠ b₂ as requested.
- `witness_20/…/100` — the conditions are satisfiable, with the exact integer quotient at (x, n) = (a₁, a₂).
- `no_full_residue_class` — the range condition 0 < x < b₁ cannot be dropped (for fixed n only finitely many x divide the nonzero 36n³ − 19), so x is pinned to the representative a₁ while n ranges over its whole infinite class.
`RESULTS.md` lists all the updated explicit constants and quotients.
# Summary of changes for run 5a59fbdb-5781-49c5-93bd-300b03a31727
## What was produced
For each requested digit size d ∈ {20, 40, 60, 80, 100} I constructed four d-digit numbers a₁, b₁, a₂, b₂ and proved in Lean (file `RequestProject/Main.lean`, builds cleanly, no `sorry`, only the standard axioms) that
  x ≡ a₁ (mod b₁), 0 < x < b₁, and n ≡ a₂ (mod b₂)  ⟹  x ∣ 36n³ − 19,
i.e. (36n³ − 19)/x is an integer. The explicit constants are listed in `RESULTS.md`; e.g. for d = 20:
a₁ = b₂ = 32246011806414236081, b₁ = 64492023612828472162, a₂ = 20421157369633533309.
**Construction.** a₁ = b₂ = p, a prime with p ≡ 2 (mod 3) — so cubing is a bijection mod p and 36a₂³ ≡ 19 (mod p) has a solution a₂, which is the n-congruence. b₁ = 2p, so the congruence class of x modulo b₁, intersected with (0, b₁), is exactly x = p. Then every n ≡ a₂ (mod p) gives p ∣ 36n³ − 19.
**Theorems in the file**
- `int_div_of_congruences` — the general criterion behind all five families.
- `fraction_integer_20/40/60/80/100` — the five congruence statements above, with explicit numerals.
- `digits_20/…/100` — machine-checked proof that all four constants of each family have exactly d decimal digits.
- `witness_20/…/100` — the conditions are satisfiable: the pair (x, n) = (a₁, a₂) meets them, together with the exact integer quotient (36a₂³ − 19)/a₁.
- `no_full_residue_class` — a correctness caveat, proved: the range condition 0 < x < b₁ cannot be removed. For any fixed n, 36n³ − 19 is nonzero, so only finitely many x divide it; hence no *infinite* residue class of positive x can work. The x-congruence therefore pins x to the representative a₁ of its class, while n genuinely ranges over the whole infinite class a₂ + b₂ℤ.
Your request mentioned "congruences of m, k", but the displayed fraction involves only n and x, so I formalized the congruences for x and n as written in the formula.
