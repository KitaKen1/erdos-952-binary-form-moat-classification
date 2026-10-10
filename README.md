# Gaussian moat variants and binary-form classification in Lean 4

[Erdős Problem 952](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/952.lean)
is the following statement:

> **Conjecture 1 (Gaussian moat).** Does there exist an infinite sequence of pairwise
> distinct Gaussian primes $`z_0,z_1,\ldots\in\mathbb Z[i]`$ and a finite
> $`D\ge0`$ such that
>
> ```math
> |z_{n+1}-z_n|\le D\qquad\text{for every }n\ge0?
> ```

Regarding Erdős Problem 952, this repository proposes Conjectures 3 and 4
and provides their Lean 4 proofs, as summarized in the table below:

| Conjecture | Relation to Erdős Problem 952 | Proposed by | Solved by |
|---|---|---|---|
| Conjecture 1 **Gaussian moat (Erdős Problem 952)** | Original problem | [Basil Gordon and Motzkin](https://www.renyi.hu/~p_erdos/1977-27.pdf#page=27) | OpenAI |
| Conjecture 2 **Uniform Gaussian moat** | Solving Conjecture 2 also resolves Conjecture 1. | OpenAI | OpenAI |
| Conjecture 3 **Generalized moat** | Solving Conjecture 3 also resolves Conjectures 2 and 1. | This repository | This repository |
| Conjecture 4 **Binary-form classification** | Solving Conjecture 4 also resolves Conjectures 3, 2, and 1. | This repository | This repository |

Contributions:

1. **Formal Conjecture style formalizations of Conjecture 2 (OpenAI's uniform variant),
   Conjecture 3 (the generalized binary-form variant), and Conjecture 4 (the binary-form classification).**
   (The original Erdős Problem 952, corresponding to Conjecture 1, is already included
   in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/952.lean).)
2. **Complete Lean 4 proofs of Conjectures 3 and 4.**
   (OpenAI has already formalized Conjecture 2 in Lean.)

**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-952-binary-form-moat-classification%2Fmain%2Flean4web%2FBinaryFormMoatLean4Web.lean)
(Lean **v4.35.0-rc4**, the same FC definitions and target statements).

## Conjecture statements

### Conjecture statements

Regarding Conjecture 2, the uniform Gaussian moat, OpenAI solved Erdős Problem 952,
the Gaussian moat problem. They did so by proving the following stronger
uniform statement in
[*Bounded-Step Walks on Gaussian Primes*](https://github.com/openai/math/blob/main/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf):

> **Conjecture 2 (uniform Gaussian moat).** For every finite step bound $`D\ge0`$,
> join distinct Gaussian primes whose distance is at most $`D`$.
> All connected components have a common finite size bound.

Regarding Conjecture 3, the generalized moat, this repository presents the following
conjecture, which further generalizes OpenAI's uniform Gaussian moat conjecture:

> **Conjecture 3 (generalized moat).** Let $`F\in\mathbb Z[X,Y]`$ be irreducible,
> homogeneous, and of degree at least two. For every finite $`D\ge0`$ and
> $`r\in\mathbb N`$, join distinct lattice points $`(x,y)`$ where $`F(x,y)\ne0`$
> and $`|F(x,y)|`$ has at most $`r`$ distinct prime divisors whenever their
> distance is at most $`D`$. All connected components have a common finite
> size bound, depending on $`F,D,r`$.

Regarding Conjecture 3, this repository presents a **complete Lean 4 proof of the generalized moat conjecture**.

Regarding Conjecture 4, the binary-form classification, this repository presents
the following conjecture:

> **Conjecture 4 (binary-form moat classification).** Let $`F\in\mathbb Z[X,Y]`$
> be nonzero and homogeneous of positive degree. Arbitrarily long finite
> injective walks through lattice points $`(x,y)`$ where $`F(x,y)\ne0`$
> and $`|F(x,y)|`$ has at most $`r`$ distinct prime divisors exist for some
> fixed $`D\ge0`$ and $`r\in\mathbb N`$, with steps at most $`D`$,
> if and only if there are $`c,a,b\in\mathbb Z`$ and $`m\in\mathbb N`$ such that
>
> ```math
> F=c(aX+bY)^m,\qquad
> c\ne0,\quad(a,b)\ne(0,0),\quad m>0.
> ```

Regarding Conjecture 4, this repository presents a **complete Lean 4 proof of the binary-form classification theorem**.

### Comparison of conditions

The column **Polynomial F(X,Y)** specifies the integer polynomial associated
with each conjecture. All forms lie in $`\mathbb Z[X,Y]`$.

| Conjecture | Permitted points | Polynomial<br>F(X,Y) | Irr | Hom | $`d`$ | Conclusion |
|---|---|---|---|---|---|---|
| **1. Gaussian<br>moat** | Gaussian primes | X² + Y² | ✓ | ✓ | $`2`$ | **Negative** |
| **2. Uniform<br>Gaussian moat** | Gaussian primes | X² + Y² | ✓ | ✓ | $`2`$ | **Negative** |
| **3. Generalized<br>moat** | Lattice points with $`F(x,y)\ne0`$ and at most $`r`$ distinct prime divisors of $`\lvert F(x,y)\rvert`$ | F ∈ ℤ[X,Y] | ✓ | ✓ | $`d\ge2`$ | **Negative** |
| **4. Binary-form<br>classification** | Lattice points with $`F(x,y)\ne0`$ and at most $`r`$ distinct prime divisors of $`\lvert F(x,y)\rvert`$ | F ∈ ℤ[X,Y]<br>F ≠ 0 | — | ✓ | $`d\ge1`$ | **Positive** iff<br>linear power;<br>**negative**<br>otherwise. |

**Irr** means irreducible in $`\mathbb Z[X,Y]`$;
**Hom** means homogeneous of degree $`d`$.
✓ means the property holds; — means no requirement. In the first two rows,
$`F`$ records the Gaussian norm.

Answers concern infinite injective walks in Conjecture 1 and arbitrarily long
finite injective walks in Conjectures 2–4, with the applicable bounds fixed.
A **linear power** is $`F=c(aX+bY)^m`$ with
$`c,a,b\in\mathbb Z,\;c\ne0,\;(a,b)\ne(0,0),\;m\in\mathbb N_{>0}`$.

### Implications

**Conjecture 2 gives a negative answer to Conjecture 1.** An infinite injective
Gaussian-prime walk with a fixed step bound would lie in a single connected
component and contain infinitely many distinct vertices. Conjecture 2 gives
a finite size bound for that component, which rules out such a walk.

**Conjecture 3 implies Conjecture 2.** Take $`F=X^2+Y^2`$ and $`r=1`$.
Every Gaussian prime has norm equal to a rational prime or its square, so
every Gaussian prime is a permitted point for this choice of $`F,r`$.
Each Gaussian-prime component is contained in a component of this larger
graph and inherits its common finite size bound.

**Conjecture 4 implies Conjecture 3.** An irreducible form of degree at least
two cannot equal $`c(aX+bY)^m`$: $`m=1`$ would give degree one, and $`m\ge2`$
would make the form reducible. The classification therefore rules out
arbitrarily long finite injective walks for every fixed $`D,r`$.
On the integer lattice, this bounds all shortest-path lengths, placing each
component in a ball of common finite radius and giving a common finite size bound.

## Formal Conjectures like lean targets

Regarding Conjecture 2, [OpenAIVariant.lean](FClikelean/OpenAIVariant.lean)
states OpenAI's uniform variant in the sequence notation of FC 952:

```lean
@[category research solved, AMS 5 11]
theorem erdos_952_openai : answer(False) ↔
  ∃ C : ℤ, ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
    Function.Injective x ∧
      ∀ n ≤ N, Prime (x n) ∧ (n < N → (x (n + 1) - x n).norm < C) := by
  sorry
```

Regarding Conjecture 3, [GeneralizedVariant.lean](FClikelean/GeneralizedVariant.lean)
replaces Gaussian primality by a nonzero binary-form value with a finite
budget of distinct prime factors:

```lean
def FewPrimeFactors (F : MvPolynomial (Fin 2) ℤ) (r : ℕ) (z : GaussianInt) : Prop :=
  let n := F.eval ![z.re, z.im]
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

@[category research solved, AMS 5 11]
theorem erdos_952_openai_generalized_variant : answer(False) ↔
  ∃ (F : MvPolynomial (Fin 2) ℤ) (d r : ℕ) (C : ℤ),
    Irreducible F ∧ 2 ≤ d ∧ F.IsHomogeneous d ∧
      ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
        Function.Injective x ∧
          ∀ n ≤ N, FewPrimeFactors F r (x n) ∧
            (n < N → (x (n + 1) - x n).norm < C) := by
  sorry
```

The Formal Conjecture style files use `by sorry` as statement placeholders. Their matching
complete proofs are in [OpenAIVariant.lean](lean/OpenAIVariant.lean) and
[GeneralizedVariant.lean](lean/GeneralizedVariant.lean), each ending with
`#print axioms` for its target.

Regarding Conjecture 4, the independent target in
[BinaryFormMoatClassification.lean](FClikelean/BinaryFormMoatClassification.lean)
uses the same `FewPrimeFactors` definition:

```lean
@[category research solved, AMS 5 11]
theorem binary_form_moat_classification :
  ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ),
    F ≠ 0 → 0 < d → F.IsHomogeneous d →
      ((∃ (r : ℕ) (C : ℤ), ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
        Function.Injective x ∧
          ∀ n ≤ N, FewPrimeFactors F r (x n) ∧
            (n < N → (x (n + 1) - x n).norm < C)) ↔
        ∃ (c a b : ℤ) (m : ℕ), c ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0) ∧ 0 < m ∧
          F = MvPolynomial.C c *
            (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
             MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ m) := by
  sorry
```

The complete proof is in
[BinaryFormMoatClassification.lean](lean/BinaryFormMoatClassification.lean),
ending with `#print axioms`. The underlying classification is in
[Moat/Conjectures.lean](lean/Moat/Conjectures.lean).

## Mathematical explanation (AI generated)

The following sketch explains the generalized moat proof and its extension
to the classification. Details are in the [manuscript](PDF/binary-form-moat.pdf).
Write $`\omega(n)`$ for the number of distinct rational prime divisors of
$`n\ge1`$, and set

```math
U_F(r)=\{z\in\mathbb Z^2:F(z)\ne0,\ \omega(|F(z)|)\le r\}.
```

We seek a bound $`B(F,D,r)`$ on the sizes of all components of the graph
on $`U_F(r)`$ with edges of length at most $`D`$. It must be independent
of the starting vertex. For $`D<1`$, every component is a singleton.

### 1. The irreducible case: a finite-sieve lemma

Let $`f\in\mathbb Z[T]`$ be irreducible of degree $`d\ge2`$ and let
$`H(X,Y)=Y^df(X/Y)`$ be its homogenization. The central lemma is:
for every $`D\ge1`$ and every finite set of excluded primes $`S`$, there
is a finite prime set $`P`$, disjoint from $`S`$, such that

```math
\mathcal A_H(P)=\{z\in\mathbb Z^2:p\nmid H(z)\text{ for all }p\in P\}
```

contains no infinite self-avoiding walk with steps at most $`D`$.
The set $`P`$ depends only on $`f,D,S`$ and is chosen before the walk.

Here is the mechanism behind this lemma. Chebotarev supplies
$`\asymp_f T/\log T`$ good completely splitting primes in $`[T,2T]`$.
At each such prime, the $`d`$ distinct roots give additive projections

```math
\phi_{p,j}(x,y)=x-\rho_{p,j}y\pmod p,
\qquad
H(x,y)=a_d\prod_{j=1}^d\phi_{p,j}(x,y)\pmod p.
```

Thus avoiding divisibility by $`p`$ means avoiding zero in every root
projection. Irreducibility also gives, for every nonzero lattice vector,
$`0<|H(v)|\le C_f\|v\|^d`$. For a primitive vector $`v`$, a uniformly
chosen root at a fixed prime annihilates $`v`$ with probability at most
$`1/d`$. The product of the primes that can annihilate it divides
$`H(v)`$. Moreover, primes annihilating two vectors divide their
determinant. These facts control collisions of random root projections
in thin rectangles.

Fix a hypothetical avoiding walk and randomize only sampled times and
auxiliary root choices. Geometric estimates for the differences along
self-avoiding segments, together with the collision bounds, enrich the
joint residue entropy. Iterating this enrichment and transferring
coverage between checkpoints gives estimates for the residues visited
by future segments. A common sampling schedule keeps the displacement
and conditioning costs small.

To see how zero avoidance costs information, let $`W_L`$ be a word of
$`L`$ successive increments. It determines all displacements from the
starting point, whose root residue must satisfy

```math
\phi_{p,j}(z_t)\notin
\{-\phi_{p,j}(z_{t+s}-z_t):0\le s\le L\}.
```

When $`C_f(DL)^d<p`$, the projected vertices of this word are distinct:
a collision would make $`p`$ divide a nonzero integer $`H(v)`$ of
absolute value smaller than $`p`$. The joint entropy and coverage
estimates turn these restrictions into a quantitative information
cost. For a batch at scale $`T`$, let $`X_T`$ be its selected starting
residues and $`O_T`$ the residues from earlier batches. Suitable word
lengths $`L_T`$ give

```math
\frac{\mathbb E I(X_T;W_{L_T}\mid O_T)}{L_T}
\ge \frac{c_{f,D}}{\log T},\qquad c_{f,D}>0.
```

All batches are compared under the same smoothed sampling law. Nested
residue observations and word lengths let the entropy chain rule
telescope these costs:

```math
\sum_T\frac{\mathbb E I(X_T;W_{L_T}\mid O_T)}{L_T}
\le \log K_D+o(1),
```

where $`K_D`$ is the finite number of possible lattice increments.
The chosen scale families make $`\sum_T1/\log T`$ arbitrarily large,
contradicting this fixed entropy budget. All thresholds are uniform
over the hypothetical walks, so one finite union of prime batches
works for every walk. This proves the finite-sieve lemma; its Lean
exit is [PaperPrimeUnionWalkExit435.lean](lean/Integrations/PaperPrimeUnionWalkExit435.lean).

### 2. From the sieve to every prime-factor budget

The avoiding set is periodic modulo $`Q=\prod_{p\in P}p`$.
Its bounded-step graph is locally finite, so König's lemma turns the
absence of infinite simple paths into finiteness of every component.
A finite component cannot contain two distinct points congruent
modulo $`Q`$: their difference would translate that component onto
itself, forcing it to be infinite. Consequently each component has
at most $`Q^2`$ vertices.

For a budget $`r`$, construct $`r+1`$ disjoint prime blocks
$`P_1,\ldots,P_{r+1}`$. Every point of $`U_H(r)`$ avoids one whole
block, since meeting all blocks would supply $`r+1`$ distinct prime
divisors. Hence

```math
U_H(r)\subseteq\bigcup_{j=1}^{r+1}\mathcal A_H(P_j).
```

Construct the blocks successively. If the current union has
$`D`$-component diameter bound $`a`$, choose the next block at step
bound $`a+2D`$, excluding all previously chosen primes. If its
components at that enlarged bound have diameter at most $`b`$,
compressing excursions through the old union bounds the new union's
component diameters by $`b+2a+2D`$. Induction gives a finite diameter
bound for the whole union. Its periodicity then gives a uniform
component-size bound, which also bounds the smaller graph on
$`U_H(r)`$. See [FiniteSieveExit435.lean](lean/Integrations/FiniteSieveExit435.lean).

### 3. The generalized moat and the classification

An irreducible homogeneous binary form of degree at least two is the
homogenization of its irreducible affine polynomial $`F(T,1)`$.
The preceding argument therefore proves the generalized moat statement.
A component bound $`B`$ forbids an injective allowed walk with
$`B+1`$ vertices, giving the sequence-form target in this repository.

For the classification, divisibility gives a useful reduction:
if $`G\mid F`$, then $`U_F(r)\subseteq U_G(r)`$, so uniform bounds for
$`G`$ imply them for $`F`$. Factoring $`F(T,1)`$ and homogenizing shows
that a nonexceptional form has either a homogenized irreducible divisor
of degree at least two or two independent integer linear divisors.
The first case follows from the sieve argument. In the second, the
Chinese remainder theorem creates periodic forbidden intervals in
each linear coordinate: every integer in such an interval is divisible
by $`r+1`$ prescribed distinct primes. Choose their widths larger than
the coordinate changes along a $`D`$-step. A component stays between
successive intervals in both coordinates, and independence of the
linear forms bounds its size.

The remaining forms are exactly $`F=c(aX+bY)^m`$. They admit the
explicit injective walk

```math
z_n=(a+bn,b-an),\qquad
F(z_n)=c(a^2+b^2)^m\ne0.
```

Its step length is $`\sqrt{a^2+b^2}`$ and its prime-factor budget is
constant. This proves the exceptional direction and completes the
[classification](lean/Moat/Conjectures.lean). Taking $`F=X^2+Y^2`$
and $`r=1`$ gives uniform bounds for Gaussian primes, since the norm
of a Gaussian prime is a rational prime or the square of one.
Those bounds in turn rule out the infinite walk asked for in
Erdős Problem 952.

## Files

| Directory | Contents |
|---|---|
| [FClikelean/](FClikelean/) | Three separate Formal Conjecture style statements |
| [lean/](lean/) | Three proof entries sharing one Lean **v4.35.0-rc3** project |
| [lean4web/](lean4web/) | Complete proofs of the same three FC targets in one file, Lean **v4.35.0-rc4** |
| [PDF/](PDF/) | Companion manuscript |

## Build and verification

```bash
cd lean
lake exe cache get
lake --wfail build
```

All three proof entries were checked with Lean **v4.35.0-rc3**. Their axiom
outputs contain only `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`. [Verification record](lean/evidence/entry-points.json).

The [Lean4Web file](lean4web/BinaryFormMoatLean4Web.lean) uses the same
`FewPrimeFactors` definitions and sequence-form target statements as
[FClikelean/](FClikelean/). Its final declarations are the three target theorems,
each followed by `#print axioms`. In both standalone versions, FC's
`answer(False)` is written as `False`, and FC catalogue attributes are omitted.
Full-file verification remains incomplete after a host restart interrupted
compilation before the final axiom audits. The current file also includes a
compatibility fix for Latest Mathlib and has not been fully verified.
[Current single-file check status](lean/evidence/direct-fc-browser-verification.json).

## References

1. Paul Erdős, [*Problems and results on combinatorial number theory III*](https://www.renyi.hu/~p_erdos/1977-27.pdf),
   in *Number Theory Day*, Lecture Notes in Mathematics **626**, Springer (1977),
   pp. 43–72. The Gaussian moat problem and its attribution to Basil Gordon and
   Motzkin appear on [p. 69](https://www.renyi.hu/~p_erdos/1977-27.pdf#page=27).
2. OpenAI, [*Bounded-Step Walks on Gaussian Primes*](https://github.com/openai/math/blob/main/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf),
   September 26, 2026. The uniform Gaussian moat result underlying Conjecture 2.
3. The Formal Conjectures Authors,
   [*Erdős Problem 952*](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/952.lean),
   in Google DeepMind's *Formal Conjectures*. The original sequence-form Lean statement.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation
were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex
using GPT-6 Astra and GPT-6.1 sol.
