import Moat.Catalogue
import Moat.Conjectures

/-! The independent all-degree classification, including reducible forms. -/

namespace BinaryFormMoatClassification

/-- The form's value at $z$ is nonzero and has at most $r$ distinct prime factors. -/
def FewPrimeFactors (F : MvPolynomial (Fin 2) ℤ) (r : ℕ) (z : GaussianInt) : Prop :=
  let n := F.eval ![z.re, z.im]
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

/-- Arbitrarily long walks exist exactly for the forms $c(aX+bY)^m$. -/
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
  intro F d hF hd hhom
  constructor
  · rintro ⟨r, C, hwalk⟩
    by_contra hex
    have hmoat := (BinaryFormMoat.classification F d hF hd hhom).mpr hex
    have h := BinaryFormMoatCatalogue.no_arbitrarily_long_walks
      {z | BinaryFormMoatCatalogue.FewPrimeFactors r (F.eval ![z.1, z.2])} C
      ((BinaryFormMoatCatalogue.uniformMoat_iff F).mp hmoat C.natAbs r)
    exact h hwalk
  · rintro ⟨c, a, b, m, hc, hab, _, rfl⟩
    have hq : a^2 + b^2 ≠ 0 := by
      rcases hab with ha | hb
      · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
      · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
    let q : ℤ := c * (a^2 + b^2)^m
    have hq0 : q ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hq)
    let x : ℕ → GaussianInt := fun n => ⟨a + b * (n : ℤ), b - a * (n : ℤ)⟩
    have hx : Function.Injective x := by
      intro n k h
      apply BinaryFormMoat.fibrePoint_injective a b hab
      exact Prod.ext (congrArg Zsqrtd.re h) (congrArg Zsqrtd.im h)
    have heval (n : ℕ) :
        (MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
           MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ m).eval
          ![(x n).re, (x n).im] = q := by
      simp only [x, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      change c * (a * (a + b * (n : ℤ)) + b * (b - a * (n : ℤ))) ^ m = q
      congr 2
      ring
    refine ⟨q.natAbs.primeFactors.card, a^2 + b^2 + 1, fun N => ⟨x, hx, ?_⟩⟩
    intro n _
    constructor
    · unfold FewPrimeFactors
      rw [heval]
      exact ⟨hq0, le_rfl⟩
    · intro _
      have he : (x (n + 1) - x n).norm = a^2 + b^2 := by
        simp only [x, Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Nat.cast_add, Nat.cast_one]
        ring
      rw [he]
      omega

end BinaryFormMoatClassification

#print axioms BinaryFormMoatClassification.binary_form_moat_classification
