module

public import FormalConjecturesUtil

/-! # Generalized binary-form moat variant -/

@[expose] public section

namespace Erdos952

/-- At most $r$ distinct prime factors in the nonzero value $F(z)$. -/
def FewPrimeFactors (F : MvPolynomial (Fin 2) ℤ) (r : ℕ) (z : GaussianInt) : Prop :=
  let n := F.eval ![z.re, z.im]
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

/-- The generalized binary-form moat theorem. -/
@[category research solved, AMS 5 11]
theorem erdos_952_openai_generalized_variant : answer(False) ↔
  ∃ (F : MvPolynomial (Fin 2) ℤ) (d r : ℕ) (C : ℤ),
    Irreducible F ∧ 2 ≤ d ∧ F.IsHomogeneous d ∧
      ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
        Function.Injective x ∧
          ∀ n ≤ N, FewPrimeFactors F r (x n) ∧
            (n < N → (x (n + 1) - x n).norm < C) := by
  sorry

end Erdos952
