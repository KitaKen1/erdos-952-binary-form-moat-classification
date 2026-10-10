import Moat.BoxLineWitness
import Moat.IrreducibleValues

namespace BinaryFormMoat

/-- In a doubling interval with T ≥ 2, log p ≤ 2 log T. This deliberately
uses a coarse constant to avoid unnecessary asymptotic estimates. -/
theorem log_le_two_log_of_dyadic (T p : ℕ) (hT : 2 ≤ T) (hp : p.Prime)
    (hpT : p ≤ 2 * T) : Real.log (p : ℝ) ≤ 2 * Real.log (T : ℝ) := by
  have hT' : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have htwo : Real.log (2 : ℝ) ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  calc
    _ ≤ Real.log ((2 : ℝ) * T) :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpT)
    _ = Real.log 2 + Real.log (T : ℝ) := Real.log_mul (by norm_num) hT'.ne'
    _ ≤ _ := by linarith

/-- The sum of squared log weights is at most 4 k (log T)^2. -/
theorem dyadic_log_square_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) :
    (∑ p ∈ P, (Real.log (p : ℝ)) ^ 2) ≤ 4 * P.card * (Real.log (T : ℝ)) ^ 2 := by
  calc
    _ ≤ ∑ _p ∈ P, (2 * Real.log (T : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hle := log_le_two_log_of_dyadic T p hT (hP p hp) (hpT p hp)
      have hp0 := (hP p hp).log_pos
      nlinarith
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A gap η k log T gives an exponential rate exp(-η² k / 2).
Nonemptiness is checked rather than silently dividing by a zero variance. -/
theorem dyadic_hoeffding_rate (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hne : P.Nonempty) (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T)
    (η : ℝ) :
    Real.exp (-2 * (η * P.card * Real.log (T : ℝ)) ^ 2 /
      (∑ p ∈ P, (Real.log (p : ℝ)) ^ 2)) ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  apply Real.exp_le_exp.mpr
  have hD : 0 < ∑ p ∈ P, (Real.log (p : ℝ)) ^ 2 :=
    Finset.sum_pos (fun p hp => sq_pos_of_pos (hP p hp).log_pos) hne
  apply (div_le_iff₀ hD).mpr
  have hmul := mul_le_mul_of_nonneg_left (dyadic_log_square_sum_le P hP T hT hpT)
    (mul_nonneg (sq_nonneg η) (Nat.cast_nonneg P.card))
  nlinarith only [hmul]

/-- The fixed-line rectangle input with a direction-independent exponential
bound. A later Hamming expansion argument is still required to handle all lines. -/
theorem dyadic_box_fixed_line_tail (f : Polynomial ℤ) (d : ℕ)
    (hdeg : f.natDegree ≤ d) (hd : 0 < d)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize d) z ≠ 0)
    (R T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hgap : Real.log (R : ℝ) + Real.log (coefficientBound f d : ℝ) / d +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ)) :
    ((boxLineWitnessAssignments P S z R).card : ℝ) /
      (Fintype.piFinset (fun p : P => S p)).card ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  apply le_trans (box_fixed_line_upper_tail f d hdeg hd P hP S hcard hroot z hprim hz R
    (η * P.card * Real.log (T : ℝ)) (by positivity) hgap)
  exact dyadic_hoeffding_rate P hP hne T hT hpT η

/-- The exact irreducible input of the classification gives the same tail
bound for every primitive direction, with no assumed nonvanishing of F(v).
The universal quantifier is over separate fixed-line bounds, not their union. -/
theorem irreducible_dyadic_box_line_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (R T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hgap : Real.log (R : ℝ) + Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ)) :
    ∀ z : Point, IsCoprime z.1 z.2 →
      ((boxLineWitnessAssignments P S z R).card : ℝ) /
        (Fintype.piFinset (fun p : P => S p)).card ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  intro z hz
  exact dyadic_box_fixed_line_tail f f.natDegree le_rfl (by omega) P hP hne S hcard hroot z hz
    (irreducible_homogenization_value_ne_zero f hf hd z hz.ne_zero_or_ne_zero)
    R T hT hpT η hη hgap

end BinaryFormMoat
