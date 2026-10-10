import Moat.Catalogue
import Moat.Conjectures

/-! Complete proof of OpenAI's uniform Gaussian moat variant. -/

namespace BinaryFormMoatCatalogue

private theorem quadratic_uniformMoat :
    BinaryFormMoat.UniformMoat
      ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2 + MvPolynomial.X 1^2) := by
  let Q : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 0^2 + MvPolynomial.X 1^2
  have hQ0 : Q ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℤ)) h
    norm_num [Q] at he
  have hQhom : Q.IsHomogeneous 2 :=
    (MvPolynomial.isHomogeneous_X_pow 0 2).add (MvPolynomial.isHomogeneous_X_pow 1 2)
  apply (BinaryFormMoat.classification Q 2 hQ0 (by decide) hQhom).mpr
  rintro ⟨c, a, b, m, hc, hab, hm, he⟩
  have h := congrArg (MvPolynomial.eval (![b, -a] : Fin 2 → ℤ)) he
  simp only [Q, MvPolynomial.eval_add, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hl : a * b + b * -a = 0 := by ring
  rw [hl, zero_pow hm.ne', mul_zero] at h
  rcases hab with ha | hb
  · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
  · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]

/-- The Gaussian moat theorem, deduced from the binary-form classification. -/
private theorem gaussian_moat (R : ℕ) :
    BoundedComponents
      {z | Prime (⟨z.1, z.2⟩ : GaussianInt)} R := by
  have hQ := (uniformMoat_iff _).mp quadratic_uniformMoat R 1
  apply boundedComponents_mono (T := {z | FewPrimeFactors 1
    (((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2 +
      MvPolynomial.X 1^2).eval ![z.1, z.2])}) _ R hQ
  intro z hz
  simpa [Zsqrtd.norm, pow_two] using gaussian_prime_norm_fewPrimeFactors
    (⟨z.1, z.2⟩ : GaussianInt) hz

end BinaryFormMoatCatalogue

namespace Erdos952

private theorem no_gaussian_walks (C : ℤ) :
    ¬ ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
      Function.Injective x ∧
        ∀ n ≤ N, Prime (x n) ∧ (n < N → (x (n + 1) - x n).norm < C) := by
  have h := BinaryFormMoatCatalogue.no_arbitrarily_long_walks
    {z | Prime (⟨z.1, z.2⟩ : GaussianInt)} C
    (BinaryFormMoatCatalogue.gaussian_moat C.natAbs)
  simpa using h

/-- OpenAI's uniform strengthening in the sequence notation of FC 952. -/
theorem erdos_952_openai : False ↔
  ∃ C : ℤ, ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
    Function.Injective x ∧
      ∀ n ≤ N, Prime (x n) ∧ (n < N → (x (n + 1) - x n).norm < C) := by
  constructor
  · exact False.elim
  · rintro ⟨C, hwalk⟩
    exact no_gaussian_walks C hwalk

end Erdos952

#print axioms Erdos952.erdos_952_openai
