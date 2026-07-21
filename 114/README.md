# Sums of three cubes for 114

This folder studies integer solutions of

\[
y^2=(6n+x)^2+\frac{36n^3-19}{x}, \qquad n,x,y\in\mathbb Z,\quad x\ne0.
\]

Every such solution gives

\[
(y-x)^3+(2x+6n)^3+(-x-y)^3=114.
\]

Conversely, after labelling the unique even member of any integer solution of
\(u^3+v^3+w^3=114\) as \(v\), the inverse substitution

\[
x=-\frac{u+w}{2},\qquad y=\frac{u-w}{2},\qquad
n=\frac{u+v+w}{6}
\]

recovers an integer solution of the square equation. Thus the two problems are
equivalent.

The equation is taken from equation 7.9 of the work-in-progress
[preprint](https://figshare.com/articles/preprint/Closed_form_formulas_on_the_sums_of_three_cubes_for_k_114_192_/30509981?file=61812286).

## What the CRT construction proves

Let

\[
f(z)=36z^3-19.
\]

For every odd prime \(p\equiv2\pmod3\), cubing is a bijection modulo \(p\).
Consequently there is a unique residue \(a\pmod p\) satisfying

\[
36a^3\equiv19\pmod p.
\]

For distinct such primes \(p_i\), the Chinese remainder theorem constructs

\[
M=\prod_i p_i,\qquad A\pmod M,\qquad M\mid f(A).
\]

It follows that

\[
M\mid f(n)\qquad\text{for every }n\equiv A\pmod M.
\]

This construction is proved and numerically instantiated in
[LargeCongruences.tex](./LargeCongruences.tex), with a Lean formalization in
[Main.lean](./Main.lean).

## Correction: independent congruences do not prove the needed divisibility

Two independent conditions

\[
n\equiv B\pmod{P},\qquad x\equiv D\pmod{C}
\]

do **not** imply

\[
x\mid36n^3-19.
\]

The first condition can arrange \(P\mid f(n)\); the second can arrange
\(C\mid f(x)\). Neither connects the variable value \(x\) to \(f(n)\).

For the previously selected constants, taking \(k_1=k_2=0\) gives

\[
\begin{aligned}
n&=7668575607239450973459863267707132263860,\\
x&=609530524018264138310326718615033307496,
\end{aligned}
\]

but exact arithmetic gives

\[
(36n^3-19)\bmod x
=13003123312063609223191713487792919093\ne0.
\]

Accordingly, the earlier two-independent-class search is not presented as a
CRT reduction of the integrality condition.

There is a second reparametrization point. If

\[
n=Pk_1+B,\qquad k_1=\frac{r_1}{q_1}
\]

with \(k_1\) reduced, then

\[
q_1\mid P\quad\Longleftrightarrow\quad n\in\mathbb Z.
\]

The analogous statement holds for \(x=Ck_2+D\). Therefore allowing rational
\(k_1,k_2\) whose reduced denominators divide \(P,C\) is exactly a change of
coordinates on the original integer \((n,x)\)-search; it is not by itself a
smaller search space.

## Correct CRT specialization

Choose \(M,A\) using the proved CRT construction and set

\[
\boxed{x=M,\qquad n=A+Mt,\qquad t\in\mathbb Z.}
\]

Writing

\[
Q=\frac{36A^3-19}{M}\in\mathbb Z,
\]

the divisibility condition is now automatic for every integer \(t\), and the
remaining square condition is

\[
\boxed{
\begin{aligned}
y^2={}&36M^2t^3+36M(3A+M)t^2+12(3A+M)^2t\\
&+(6A+M)^2+Q.
\end{aligned}}
\]

This is a genuine integral-point problem on a genus-one curve.

### Integral Weierstrass model

Write the cubic as

\[
P(t)=at^3+bt^2+ct+d,
\]

where

\[
\begin{aligned}
a&=36M^2,\\
b&=36M(3A+M),\\
c&=12(3A+M)^2,\\
d&=(6A+M)^2+Q.
\end{aligned}
\]

The substitution

\[
X=at,\qquad Y=ay
\]

maps it to the integral Weierstrass equation

\[
\boxed{Y^2=X^3+bX^2+acX+a^2d.}
\]

An integral point on this Weierstrass model returns an admissible
\((t,y)\) only when

\[
a\mid X,\qquad a\mid Y.
\]

Every recovered point is checked again in the original square equation and
in the cube identity before being reported.

## Rank-guided selection of CRT moduli

The objective is not to maximize the number of digits in \(M\). The objective
is to choose CRT data whose associated elliptic curve has favorable arithmetic.
The search workflow is:

1. Generate primes \(p\equiv2\pmod3\) and their unique roots of
   \(36A^3\equiv19\pmod p\).
2. Form singleton moduli and selected CRT products \(M\).
3. Construct the Weierstrass model above and compute its global root number.
4. Prioritize root number \(-1\) as a heuristic for odd rank; this is a
   prioritization rule, not proof that a useful integral point exists.
5. Compute algebraic-rank bounds, analytic rank, and Mordell--Weil generators
   for the most promising curves.
6. Determine integral points, retaining only those in the sublattice
   \(a\mid X,Y\).
7. Independently verify every recovered \((n,x,y)\) and the resulting
   \((u,v,w)\).

Positive rank does not guarantee a relevant integral point, and rank zero does
not automatically exclude torsion points in the required sublattice. Rank and
root number are filters for allocating computation, not substitutes for the
final exact test.

The executable implementation is
[rank_guided_elliptic_search.py](./rank_guided_elliptic_search.py). With SageMath:

```bash
sage -python 114/rank_guided_elliptic_search.py \
  --primes 17,23,29,41,47,53,59,71,83,89 \
  --max-product-size 2 \
  --compute-rank \
  --analytic-rank \
  --t-bound 100000
```

For 30- or 40-digit primes, begin with root-number screening and small exact
\(t\)-ranges, then enable rank and integral-point computations selectively;
factoring conductors and proving Mordell--Weil completeness can dominate the
runtime.

## Status of the rational point with \(y=9162\)

The values

\[
n=-\frac{1506}{5},\qquad x=-\frac{61}{5},\qquad y=9162
\]

are an exact rational point, verified in
[rational_solution_y_9162.tex](./rational_solution_y_9162.tex). They give a
rational representation of 114, not an integer representation. The common
denominator \(5\) is precisely why that point does not satisfy the integer
problem.

## Related material

- [Companion repository and earlier approaches](https://github.com/JAgbanwa/heading-somewhere-with-this)
- [Large congruence PDF](./large_congruences.pdf)
- [Exact rational \(y=9162\) PDF](./rational_solution_y_9162.pdf)
