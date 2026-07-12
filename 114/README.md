From this preprint [\[1\]](https://figshare.com/articles/preprint/Closed_form_formulas_on_the_sums_of_three_cubes_for_k_114_192_/30509981?file=61812286), 

$\Biggl( -x + \sqrt{(6n + x)^2 + \frac{36n^3 - 19}{x}} \Biggl)^{3} + \Biggl( -x - \sqrt{(6n + x)^2 + \frac{36n^3 - 19}{x}} \Biggl)^{3} + \Biggl( 2x + 6n \Biggl)^{3} = 114.$ 

To ensure that integer solutions are yielded for this problem,  

$y^2 = (6n + x)^2 + \frac{36n^3 - 19}{x}$.

An important criterion in the above equation yielding integer solutions (and thus solving the sums of three cubes problem by extension) is this fraction $\frac{36n^3 - 19}{x} \in \mathbb{Z}$. It is highly anticipated that the solutions to the sums of three cubes problem for 114 are astronomically large in size, way beyond the capacity of modern day computing. Given that it is (obviously) unknown, values of $n,x$ for which the aforementioned fraction is an integer and by extension solves this sums of three cubes problem for integers, 
we search for large congruences of $n,x$ for which  $\frac{36n^3 - 19}{x} \in \mathbb{Z}$ with one of these two scenarios playing out: 

*When $n = p_1 k_1 + a_1$ and $x = p_2 k_2 + a_2$ , $k_1, k_2$ could be integers for which $y$ is an integer **or** $k_1, k_2$ could be non-integers for which $y$ is an integer (in which case $k_1 | p_1$ and $k_2 | p_2$).

I then posed this question to Anthropic's Claude Sonnet (Medium):

```
Can you search for the largest modular congruences you can find where for n = a_1(modp_1) and x = a_2(modp_2), a_1, a_2, p_1 ,p_2 could be as large as 30 digits to 40 digits long for all I care for which (36n^3 - 19)/x is integer? 
```
The resulting results can be found here; as .pdf ([\[2\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/large_congruences.pdf)) and as .tex ([\[3\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/LargeCongruences.tex)). Find the Lean formalisation of these results here [\[4\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/Main.lean).

We proceed to choose one of the congruences, preferably the 'largest' .i.e. the 40-digit long congruences of $n,x$ for which $\frac{36n^3 - 19}{x} \in \mathbb{Z}$. Thus, $n = 7729484335457653901640057298531371241781 k_1 + 7668575607239450973459863267707132263860$ and $x = 2486598372481845396683104279916570951657 k_2 + 609530524018264138310326718615033307496$. 

The earlier equation can be reframed now as:

```
y^2 = (6(7729484335457653901640057298531371241781 k_1 + 7668575607239450973459863267707132263860) + 2486598372481845396683104279916570951657 k_2 + 609530524018264138310326718615033307496)^2 + \frac{36(7729484335457653901640057298531371241781 k_1 + 7668575607239450973459863267707132263860)^3 - 19}{2486598372481845396683104279916570951657 k_2 + 609530524018264138310326718615033307496}
```
After expanding, the aforementioned equation becomes:

```
y^2 = (46376906012745923409840343791188227450686 k_1 + 2486598372481845396683104279916570951657 k_2 + 46620984167454969979069506324857826890656)^2 + \frac{16624709489189407440388643213728981685328681791089732876601710038587810847889998299944067715532425036389785803066750571476 k_1^3 + 49481117808109917372654153079508763668111544754357197384070641920072789816863012403689690888343605217704925500637542381680 k_1^2 + 49091204092562086792376670895376907696653809047079935546700717754945371359211889852498465756993689409319452027811965860800 k_1 + 16234787638949931054338904909272730014525041302296577490759268200927073136776735826378161845204226655836573767036816415981}{2486598372481845396683104279916570951657 k_2 + 609530524018264138310326718615033307496}
```

ChatGPT 5.5 Pro provided values for $k_1, k_2$ that nearly solved this problem see here ([\[5\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/rational_solution_y_9162.pdf)) ([\[6\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/rational_solution_y_9162.tex)). While the resulting values after some substitutions yield rational solutions to the sums of three cubes for 114, the dealbreaker comes from the fact that given the values for $k_1$ and $k_2$ below,

 $k_1=-\frac{38342878036197254867299316338535661320806}{38647421677288269508200286492656856208905}$ and 
 $k_2=-\frac{3047652620091320691551633593075166537541}{12432991862409226983415521399582854758285}$

we see that the denominator of $k_1$ is not a divisor of $7729484335457653901640057298531371241781$ likewise $k_2$ not being a divisor of $2486598372481845396683104279916570951657$ leaving us rational non-integer values of $n,x,y$ and thus rational non-integer solutions to this 114 problem.

A valid question to be asked is:
```
Consider that k_1 = \frac{p_1}{q_1} and k_2 = \frac{p_2}{q_2}, aside from $(k_1, k_2) = (-\frac{38342878036197254867299316338535661320806}{38647421677288269508200286492656856208905}, -\frac{3047652620091320691551633593075166537541}{12432991862409226983415521399582854758285})$, find rational solutions of (k_1, k_2) to this equation:

y^2 = (46376906012745923409840343791188227450686 k_1 + 2486598372481845396683104279916570951657 k_2 + 46620984167454969979069506324857826890656)^2 + \frac{16624709489189407440388643213728981685328681791089732876601710038587810847889998299944067715532425036389785803066750571476 k_1^3 + 49481117808109917372654153079508763668111544754357197384070641920072789816863012403689690888343605217704925500637542381680 k_1^2 + 49091204092562086792376670895376907696653809047079935546700717754945371359211889852498465756993689409319452027811965860800 k_1 + 16234787638949931054338904909272730014525041302296577490759268200927073136776735826378161845204226655836573767036816415981}{2486598372481845396683104279916570951657 k_2 + 609530524018264138310326718615033307496}

(where q_1 | 7729484335457653901640057298531371241781 and q_2 | 2486598372481845396683104279916570951657) for which $y$ is integer?
```
****************************************************

Fixed the `ring_nf` error.
The error you saw (`ring_nf made no progress`, reported at 104:102 in the online editor) came from the `class_dvd` lemma in `RequestProject/Main.lean`. When the file is pasted into the online editor without its header, that lemma's line lines up with the reported position, and its `ring` tactic is what invokes `ring_nf`. The original proof `convert dvd_add h (...) using 1 ; ring` was fragile: on a different Mathlib version, `convert ... using 1` leaves a goal shape that `ring`/`ring_nf` cannot make progress on.
I replaced it with a version-robust proof that establishes the plain polynomial identity
`36·n³ − 19 = (36·A³ − 19) + (n − A)·(36·(n² + n·A + A²))` (which `ring` always proves, since it is a genuine identity), rewrites with it, and then closes the goal with `dvd_add` together with `M ∣ n − A` (from `n ≡ A [ZMOD M]`).
The file builds cleanly with no `sorry`. Changes are committed and pushed.

Formalized the paper "Large Modular Congruences for which x ∣ 36n³ − 19" (a CRT / cube-root construction) in Lean 4 / Mathlib. All results live in `RequestProject/Main.lean` in namespace `LargeCongruences`, and the project builds cleanly with no `sorry` and only permitted axioms.
What was proved:
- **Lemma 1 (cube bijection).** `cube_bijective`: for a prime `p ≡ 2 (mod 3)`, `t ↦ t³` is a bijection of `ZMod p`; and `exists_cube_root`: every element has a cube root.
- **Construction 1.** `isUnit_thirtysix` (36 is a unit mod such `p ≠ 2`), `exists_root_zmod` (there is a residue `a` with `36a³ = 19` in `ZMod p`), and `key_single` (its integer/congruence-class form: there is `a` with `p ∣ 36n³ − 19` for all `n ≡ a (mod p)`).
- **Theorem 1 (multi-prime CRT combination).** `multiprime`: for any finite set of distinct primes each `≡ 2 (mod 3)` and `≠ 2`, with product `M`, there is a residue `A` such that `M ∣ 36n³ − 19` for every `n ≡ A (mod M)`. Proved by induction over the finite set using an explicit Bézout/CRT combination and coprimality of distinct primes (`coprime_prime_prod`).
- A generic class lemma `class_dvd` upgrading a single verified representative to an entire residue class.
- **Numerical instances (§4–§7).** All four explicit instances (two/three primes at 30 and 40 digits) are verified by exact integer arithmetic (`native_decide`): the root identities `36aᵢ³ ≡ 19 (mod pᵢ)`, the product `M = ∏ pᵢ`, the exact division `36A³ − 19 = M·Q`, and the resulting infinite family `M ∣ 36n³ − 19` for `n ≡ A (mod M)` (theorems `instance_k2_30digit`, `instance_k3_30digit`, `instance_k2_40digit`, `instance_k3_40digit`).
Note recorded in the file's docstring: primality of the 30-/40-digit `pᵢ` (checked externally in the paper) is not re-certified inside Lean, as it is computationally expensive and not needed — the family statements follow purely from the exact divisibility `M ∣ 36A³ − 19`.
Axiom check: the general theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; the numerical instances additionally use `Lean.ofReduceBool`/`Lean.trustCompiler` from `native_decide`.
