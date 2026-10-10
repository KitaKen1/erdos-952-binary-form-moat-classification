import Moat.Homogenization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Int.Basic

namespace BinaryFormMoat

/-- Unlike the bare UFD factor theorem, the chosen factor is nonconstant. -/
theorem exists_positive_degree_irreducible_divisor (p : Polynomial ℤ)
    (hp : 0 < p.natDegree) :
    ∃ q : Polynomial ℤ, Irreducible q ∧ q ∣ p ∧ 0 < q.natDegree := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hp
  | unit p hu => simp [Polynomial.natDegree_eq_zero_of_isUnit hu] at hp
  | mul p q hp0 hq ih =>
    by_cases hqpos : 0 < q.natDegree
    · exact ⟨q, hq, dvd_mul_right _ _, hqpos⟩
    · have hpdeg : 0 < p.natDegree := by
        rw [Polynomial.natDegree_mul hq.ne_zero hp0] at hp
        omega
      obtain ⟨s, hs, hsp, hsdeg⟩ := ih hpdeg
      exact ⟨s, hs, hsp.trans (dvd_mul_left _ _), hsdeg⟩

/-- Proportional degree-one factors are scalar multiples over the integers when the
first factor is irreducible. Divisibility avoids introducing rational coefficients. -/
theorem linear_factor_eq_const_mul (p q : Polynomial ℤ) (hp : Irreducible p)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 1)
    (hdet : p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1 = 0) :
    ∃ c : ℤ, c ≠ 0 ∧ q = Polynomial.C c * p := by
  have hp1 : p.coeff 1 ≠ 0 := by
    rw [← hpdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  have hq0 : q ≠ 0 := by intro h; simp [h] at hqdeg
  have he : Polynomial.C (p.coeff 1) * q = Polynomial.C (q.coeff 1) * p := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hqdeg.le]
    conv_rhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le]
    have hc : Polynomial.C (p.coeff 1) * Polynomial.C (q.coeff 0) =
        Polynomial.C (p.coeff 0) * Polynomial.C (q.coeff 1) := by
      rw [← Polynomial.C_mul, ← Polynomial.C_mul, sub_eq_zero.mp hdet]
    linear_combination hc
  have hpdvd : p ∣ q := by
    have h : p ∣ Polynomial.C (p.coeff 1) * q := by
      rw [he]
      exact dvd_mul_left _ _
    rcases hp.prime.dvd_or_dvd h with hc | hq
    · have hd := Polynomial.natDegree_le_of_dvd hc (Polynomial.C_ne_zero.mpr hp1)
      simp [hpdeg] at hd
    · exact hq
  obtain ⟨t, ht⟩ := hpdvd
  have ht0 : t ≠ 0 := by intro h; apply hq0; simp [ht, h]
  have htdeg : t.natDegree = 0 := by
    have h := Polynomial.natDegree_mul hp.ne_zero ht0
    rw [← ht, hpdeg, hqdeg] at h
    omega
  have htc := Polynomial.eq_C_of_natDegree_eq_zero htdeg
  refine ⟨t.coeff 0, ?_, ?_⟩
  · intro h; apply ht0; rw [htc, h, Polynomial.C_0]
  · conv_lhs => rw [ht, htc, mul_comm]

/-- If all nonconstant irreducible factors are scalar multiples of one polynomial,
the original polynomial is an integer constant times a power of it. -/
theorem eq_const_mul_pow_of_irreducible_divisors (p q : Polynomial ℤ) (hp : p ≠ 0)
    (hfactors : ∀ i : Polynomial ℤ, Irreducible i → i ∣ p →
      i.natDegree = 0 ∨ ∃ c : ℤ, c ≠ 0 ∧ i = Polynomial.C c * q) :
    ∃ (c : ℤ) (m : ℕ), c ≠ 0 ∧ p = Polynomial.C c * q^m := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit p hu =>
    have he := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
    refine ⟨p.coeff 0, 0, ?_, by simpa using he⟩
    intro h; apply hp; rw [he, h, Polynomial.C_0]
  | mul p i hp0 hi ih =>
    obtain ⟨c, m, hc, hpEq⟩ := ih hp0 (fun j hj hjp =>
      hfactors j hj (hjp.trans (dvd_mul_left _ _)))
    rcases hfactors i hi (dvd_mul_right _ _) with hdeg | ⟨b, hb, hiEq⟩
    · have hiEq := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hb : i.coeff 0 ≠ 0 := by
        intro h; apply hi.ne_zero; rw [hiEq, h, Polynomial.C_0]
      refine ⟨i.coeff 0 * c, m, mul_ne_zero hb hc, ?_⟩
      conv_lhs => rw [hiEq, hpEq]
      rw [Polynomial.C_mul]
      ring
    · refine ⟨b * c, m + 1, mul_ne_zero hb hc, ?_⟩
      rw [hiEq, hpEq, Polynomial.C_mul, pow_succ]
      ring

/-- The exact high-degree input remaining after the algebraic classification. -/
def HasHighDegreeIrreducibleDivisor (F : Form) : Prop :=
  ∃ p : Polynomial ℤ, Irreducible p ∧ 2 ≤ p.natDegree ∧ p ∣ dehomogenize F

/-- The elementary branch already proved by CRT. -/
def HasIndependentLinearDivisors (F : Form) : Prop :=
  ∃ a b c d : ℤ, a * d - b * c ≠ 0 ∧ linearForm a b ∣ F ∧ linearForm c d ∣ F

/-- A degree-one factor in the affine chart gives a linear divisor of the form. -/
theorem linear_divisor_of_chart_factor (F : Form) (d : ℕ) (hF : F.IsHomogeneous d)
    (p : Polynomial ℤ) (hp : p ∣ dehomogenize F) (hpdeg : p.natDegree = 1) :
    linearForm (p.coeff 1) (p.coeff 0) ∣ F := by
  have h := homogenized_divisor_dvd F d hF p hp
  rwa [hpdeg, homogenize_one_eq_linearForm p hpdeg.le] at h

/-- Every non-exceptional homogeneous form has either two independent linear divisors
or the homogenization of a nonconstant irreducible polynomial of degree at least two.
This is a full algebraic reduction; it assumes no moat theorem for the latter branch. -/
theorem homogeneous_factor_dichotomy (F : Form) (d : ℕ) (h0 : F ≠ 0)
    (hd : 0 < d) (hF : F.IsHomogeneous d) (hex : ¬ IsLinearPower F) :
    HasIndependentLinearDivisors F ∨ HasHighDegreeIrreducibleDivisor F := by
  classical
  by_cases hlin : HasIndependentLinearDivisors F
  · exact Or.inl hlin
  right
  by_contra hhigh
  let p := dehomogenize F
  have hp0 : p ≠ 0 := dehomogenize_ne_zero F d hF h0
  have hpdeg : 0 < p.natDegree := by
    by_contra h
    exact hex (isLinearPower_of_dehomogenize_degree_zero F d h0 hd hF
      (by change p.natDegree = 0; omega))
  have hsmall (q : Polynomial ℤ) (hq : Irreducible q) (hqp : q ∣ p) : q.natDegree ≤ 1 := by
    by_contra h
    exact hhigh ⟨q, hq, by omega, hqp⟩
  obtain ⟨q, hq, hqp, hqpos⟩ := exists_positive_degree_irreducible_divisor p hpdeg
  have hqdeg : q.natDegree = 1 := by have := hsmall q hq hqp; omega
  have hq1 : q.coeff 1 ≠ 0 := by
    rw [← hqdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero
  have hqF := linear_divisor_of_chart_factor F d hF q hqp hqdeg
  have hfactors (i : Polynomial ℤ) (hi : Irreducible i) (hip : i ∣ p) :
      i.natDegree = 0 ∨ ∃ c : ℤ, c ≠ 0 ∧ i = Polynomial.C c * q := by
    by_cases hi0 : i.natDegree = 0
    · exact Or.inl hi0
    right
    have hideg : i.natDegree = 1 := by have := hsmall i hi hip; omega
    apply linear_factor_eq_const_mul q i hq hqdeg hideg
    by_contra hdet
    exact hlin ⟨q.coeff 1, q.coeff 0, i.coeff 1, i.coeff 0, hdet, hqF,
      linear_divisor_of_chart_factor F d hF i hip hideg⟩
  obtain ⟨c, m, hc, hpEq⟩ := eq_const_mul_pow_of_irreducible_divisors p q hp0 hfactors
  have hpDegree : p.natDegree = m := by
    rw [hpEq, Polynomial.natDegree_C_mul hc, Polynomial.natDegree_pow, hqdeg, mul_one]
  have hmpos : 0 < m := by omega
  have hpd : p.natDegree ≤ d := natDegree_dehomogenize_le F d hF
  have hdm : d = m := by
    by_contra hne
    have hgap : 0 < d - p.natDegree := by omega
    have hY : (MvPolynomial.X (1 : Fin 2) : Form) ∣ F := by
      rw [homogeneous_chart_factorization F d hF]
      exact (dvd_pow_self _ (show d - (dehomogenize F).natDegree ≠ 0 by
        change d - p.natDegree ≠ 0; omega)).trans
        (dvd_mul_left _ _)
    apply hlin
    refine ⟨q.coeff 1, q.coeff 0, 0, 1, ?_, hqF, ?_⟩
    · simpa using hq1
    · simpa [linearForm] using hY
  have hrepr : F = MvPolynomial.C c * (linearForm (q.coeff 1) (q.coeff 0))^m := by
    calc
      F = p.homogenize d := (homogenize_dehomogenize F d hF).symm
      _ = (Polynomial.C c * q^m).homogenize m := by rw [hpEq, hdm]
      _ = MvPolynomial.C c * (q.homogenize 1)^m := by
        rw [Polynomial.homogenize_C_mul]
        congr 1
        simpa only [hqdeg, one_mul] using homogenize_pow_natDegree q m
      _ = _ := by rw [homogenize_one_eq_linearForm q hqdeg.le]
  apply hex
  exact ⟨c, q.coeff 1, q.coeff 0, m, hc, Or.inl hq1, hmpos, hrepr⟩

/-- Proving only the high-degree univariate irreducible case suffices for every degree. -/
theorem uniformMoat_of_irreducible_case
    (hirr : ∀ p : Polynomial ℤ, Irreducible p → 2 ≤ p.natDegree →
      UniformMoat (p.homogenize p.natDegree))
    (F : Form) (d : ℕ) (h0 : F ≠ 0) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hex : ¬ IsLinearPower F) : UniformMoat F := by
  rcases homogeneous_factor_dichotomy F d h0 hd hF hex with hlin | hhigh
  · obtain ⟨a, b, c, e, hdet, h₁, h₂⟩ := hlin
    exact uniformMoat_of_independent_linear_divisors F a b c e hdet h₁ h₂
  · obtain ⟨p, hp, hpdeg, hpF⟩ := hhigh
    exact uniformMoat_of_dehomogenized_divisor F d hF p hpF (hirr p hp hpdeg)

end BinaryFormMoat
