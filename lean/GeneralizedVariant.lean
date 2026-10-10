import Moat.Catalogue
import Moat.Conjectures

/-! Complete proof of the generalized binary-form moat variant. -/

namespace Erdos952

/-- The form's value at $z$ is nonzero and has at most $r$ distinct prime factors. -/
def FewPrimeFactors (F : MvPolynomial (Fin 2) ℤ) (r : ℕ) (z : GaussianInt) : Prop :=
  let n := F.eval ![z.re, z.im]
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

/-- The binary-form generalization at every finite prime-factor budget. -/
theorem erdos_952_openai_generalized_variant : False ↔
  ∃ (F : MvPolynomial (Fin 2) ℤ) (d r : ℕ) (C : ℤ),
    Irreducible F ∧ 2 ≤ d ∧ F.IsHomogeneous d ∧
      ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
        Function.Injective x ∧
          ∀ n ≤ N, FewPrimeFactors F r (x n) ∧
            (n < N → (x (n + 1) - x n).norm < C) := by
  constructor
  · exact False.elim
  · rintro ⟨F, d, r, C, hF, hd, hhom, hwalk⟩
    have hdeg : F.totalDegree = d := hhom.totalDegree hF.ne_zero
    let f : BinaryFormMoatCatalogue.NonlinearIrreducibleForm :=
      ⟨F, hF, by simpa only [hdeg] using hhom, by omega⟩
    have hmoat := (BinaryFormMoat.classification F d hF.ne_zero (by omega) hhom).mpr
      (BinaryFormMoatCatalogue.nonlinear_not_isLinearPower f)
    have h := BinaryFormMoatCatalogue.no_arbitrarily_long_walks
      {z | BinaryFormMoatCatalogue.FewPrimeFactors r (F.eval ![z.1, z.2])} C
      ((BinaryFormMoatCatalogue.uniformMoat_iff F).mp hmoat C.natAbs r)
    exact h hwalk

end Erdos952

#print axioms Erdos952.erdos_952_openai_generalized_variant
