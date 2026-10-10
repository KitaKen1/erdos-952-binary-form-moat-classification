module

public import FormalConjecturesUtil

/-! # Binary-form moat classification -/

@[expose] public section

namespace BinaryFormMoatClassification

/-- At most $r$ distinct prime factors in the nonzero value $F(z)$. -/
def FewPrimeFactors (F : MvPolynomial (Fin 2) ℤ) (r : ℕ) (z : GaussianInt) : Prop :=
  let n := F.eval ![z.re, z.im]
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

/-- Arbitrarily long walks exist exactly for the forms $c(aX+bY)^m$. -/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/KitaKen1/erdos-952-binary-form-moat-classification/blob/b0b614662c342e2610fdfe6897691f9b54d33afb/lean/BinaryFormMoatClassification.lean#L14"]
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

end BinaryFormMoatClassification
