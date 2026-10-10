# Gaussian moat variants and binary-form classification in Lean 4

Three related results, each with its own FC-style statement and complete Lean proof.

| Result | FC-style statement | Complete proof |
|---|---|---|
| OpenAI's uniform Gaussian moat variant | [OpenAIVariant.lean](OpenAIVariant.lean) | [OpenAIVariant.lean](../lean/OpenAIVariant.lean) |
| The generalized binary-form variant | [GeneralizedVariant.lean](GeneralizedVariant.lean) | [GeneralizedVariant.lean](../lean/GeneralizedVariant.lean) |
| The independent all-degree binary-form classification | [BinaryFormMoatClassification.lean](BinaryFormMoatClassification.lean) | [BinaryFormMoatClassification.lean](../lean/BinaryFormMoatClassification.lean) |

The uniform Gaussian moat variant asks whether one fixed step bound supports
arbitrarily long finite injective Gaussian-prime walks. Its negative answer
follows from OpenAI's [uniform Gaussian moat theorem](https://github.com/openai/math/blob/main/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf).

The generalized variant replaces Gaussian primality by a nonzero value of
an irreducible homogeneous binary form of degree at least two whose values
have at most a fixed finite number of distinct prime factors. It also has a negative answer.

The classification treats every nonzero homogeneous binary form of positive
degree, including reducible forms. It implies the generalized variant;
that variant implies OpenAI's uniform form.

The FC-style files use `by sorry` as catalogue placeholders. The matching
proof entries have complete proofs and each ends with `#print axioms` for its target.

## Build

The three proof entries share one Lean **v4.35.0-rc3** project.

```bash
cd ../lean
lake exe cache get
lake --wfail build
```

[Entry-point verification](../lean/evidence/entry-points.json).
[Original core build and kernel-check records](../lean/evidence/build_results.json).

[Lean4Web: complete proofs of the same FC targets in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-952-binary-form-moat-classification%2Fmain%2Flean4web%2FBinaryFormMoatLean4Web.lean)
uses Lean **v4.35.0-rc4**. The single-file and modular versions use the definitions
and finite injective-sequence target statements from these FC files. Each final
target theorem is followed by `#print axioms`. FC's `answer(False)` is written
as `False` in the standalone proofs; FC catalogue attributes are omitted.
The current single-file compilation was interrupted by a host restart and has
not completed verification; see the [check status](../lean/evidence/direct-fc-browser-verification.json).

## Appendix: classification theorem

Arbitrarily long finite injective walks at some fixed step bound and
prime-factor budget exist exactly for the exceptional forms
$`F=c(aX+bY)^m`$, where $`c\ne0`$, $`(a,b)\ne(0,0)`$, and $`m>0`$.
Every other nonzero homogeneous form of positive degree has uniform finite
component-size bounds at every fixed step bound and prime-factor budget.

The independent [FC-style target](BinaryFormMoatClassification.lean) is:

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

The complete proof is
`BinaryFormMoatClassification.binary_form_moat_classification` in
[lean/BinaryFormMoatClassification.lean](../lean/BinaryFormMoatClassification.lean).
Its underlying classification is in [Moat/Conjectures.lean](../lean/Moat/Conjectures.lean).
The [companion manuscript](../PDF/binary-form-moat.pdf) gives the mathematical argument.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation
were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex
using GPT-6 Astra and GPT-6.1 sol.
