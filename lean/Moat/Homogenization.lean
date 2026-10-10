import Moat.LinearFactors
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace BinaryFormMoat

/-- The affine chart Y = 1. -/
noncomputable def dehomogenize (F : Form) : Polynomial ℤ :=
  MvPolynomial.aeval ![Polynomial.X, 1] F

/-- Dehomogenizing a degree-d homogeneous form has univariate degree at most d. -/
theorem natDegree_dehomogenize_le (F : Form) (d : ℕ) (hF : F.IsHomogeneous d) :
    (dehomogenize F).natDegree ≤ d := by
  classical
  unfold dehomogenize
  rw [F.as_sum]
  simp only [MvPolynomial.aeval_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hdegree := hF.degree_eq_sum_deg_support hm
  have hm0 : m 0 ≤ d := by
    rw [hdegree]
    by_cases hz : m 0 = 0
    · simp [hz]
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)
  have hprod : m.prod (fun i k => (![Polynomial.X, 1] : Fin 2 → Polynomial ℤ) i ^ k) =
      Polynomial.X ^ m 0 := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp
  simp only [MvPolynomial.aeval_monomial, hprod, Polynomial.algebraMap_eq]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simpa using hm0)

/-- Homogenization recovers the whole homogeneous form, including its Y-power factor. -/
theorem homogenize_dehomogenize (F : Form) (d : ℕ) (hF : F.IsHomogeneous d) :
    (dehomogenize F).homogenize d = F :=
  Polynomial.homogenize_eq_of_isHomogeneous hF rfl

theorem dehomogenize_ne_zero (F : Form) (d : ℕ) (hF : F.IsHomogeneous d) (h0 : F ≠ 0) :
    dehomogenize F ≠ 0 := by
  intro h
  have he := homogenize_dehomogenize F d hF
  rw [h, Polynomial.homogenize_zero] at he
  exact h0 he.symm

/-- Raising the homogenization degree only multiplies by a power of Y. -/
theorem homogenize_raise_degree (p : Polynomial ℤ) (n k : ℕ) (hn : p.natDegree ≤ n) :
    p.homogenize (n + k) = p.homogenize n * (MvPolynomial.X (1 : Fin 2))^k := by
  simpa using Polynomial.homogenize_mul p 1 hn (show (1 : Polynomial ℤ).natDegree ≤ k by simp)

/-- Homogenizing at the expected degree commutes with powers. -/
theorem homogenize_pow_natDegree (p : Polynomial ℤ) (m : ℕ) :
    (p^m).homogenize (p.natDegree * m) = (p.homogenize p.natDegree)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ, Polynomial.homogenize_mul _ _
      (by simp [Polynomial.natDegree_pow, Nat.mul_comm]) le_rfl, ih, pow_succ]

/-- Explicitly separates the Y factor lost in the affine chart. -/
theorem homogeneous_chart_factorization (F : Form) (d : ℕ) (hF : F.IsHomogeneous d) :
    F = (dehomogenize F).homogenize (dehomogenize F).natDegree *
      (MvPolynomial.X (1 : Fin 2))^(d - (dehomogenize F).natDegree) := by
  rw [← homogenize_raise_degree _ _ _ le_rfl,
    Nat.add_sub_of_le (natDegree_dehomogenize_le F d hF), homogenize_dehomogenize F d hF]

/-- A univariate divisor lifts to an integer polynomial divisor of the original form. -/
theorem homogenized_divisor_dvd (F : Form) (d : ℕ) (hF : F.IsHomogeneous d)
    (p : Polynomial ℤ) (hp : p ∣ dehomogenize F) : p.homogenize p.natDegree ∣ F := by
  rw [homogeneous_chart_factorization F d hF]
  exact (Polynomial.homogenize_dvd hp).trans (dvd_mul_right _ _)

/-- Arithmetic only needs to establish the moat theorem for one univariate factor. -/
theorem uniformMoat_of_dehomogenized_divisor (F : Form) (d : ℕ) (hF : F.IsHomogeneous d)
    (p : Polynomial ℤ) (hp : p ∣ dehomogenize F)
    (hmoat : UniformMoat (p.homogenize p.natDegree)) : UniformMoat F :=
  uniformMoat_of_dvd F _ (homogenized_divisor_dvd F d hF p hp) hmoat

/-- A polynomial of degree at most one homogenizes to its explicit linear form. -/
theorem homogenize_one_eq_linearForm (p : Polynomial ℤ) (hp : p.natDegree ≤ 1) :
    p.homogenize 1 = linearForm (p.coeff 1) (p.coeff 0) := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hp]
  simp only [Polynomial.homogenize_add, Polynomial.homogenize_C_mul,
    Polynomial.homogenize_X (by decide : 1 ≠ 0), Nat.sub_self, pow_zero, mul_one,
    Polynomial.homogenize_C, pow_one, linearForm]

/-- Every nonzero homogeneous form of degree one is exceptional. -/
theorem isLinearPower_of_degree_one (F : Form) (h0 : F ≠ 0) (hF : F.IsHomogeneous 1) :
    IsLinearPower F := by
  have he : F = linearForm ((dehomogenize F).coeff 1) ((dehomogenize F).coeff 0) := by
    exact (homogenize_dehomogenize F 1 hF).symm.trans
      (homogenize_one_eq_linearForm _ (natDegree_dehomogenize_le F 1 hF))
  refine ⟨1, (dehomogenize F).coeff 1, (dehomogenize F).coeff 0, 1, one_ne_zero, ?_,
    Nat.zero_lt_one, ?_⟩
  · by_contra h
    push Not at h
    apply h0
    rw [he, h.1, h.2]
    simp [linearForm]
  · simpa only [MvPolynomial.C_1, pow_one, one_mul, linearForm] using he

/-- A constant affine chart can only come from a pure power of Y. -/
theorem isLinearPower_of_dehomogenize_degree_zero (F : Form) (d : ℕ)
    (h0 : F ≠ 0) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hp : (dehomogenize F).natDegree = 0) : IsLinearPower F := by
  have he : dehomogenize F = Polynomial.C ((dehomogenize F).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hp
  have hc : (dehomogenize F).coeff 0 ≠ 0 := by
    intro h
    apply dehomogenize_ne_zero F d hF h0
    rw [he, h, Polynomial.C_0]
  refine ⟨(dehomogenize F).coeff 0, 0, 1, d, hc, Or.inr one_ne_zero, hd, ?_⟩
  have hh := homogenize_dehomogenize F d hF
  rw [he, Polynomial.homogenize_C] at hh
  simpa using hh.symm

end BinaryFormMoat
