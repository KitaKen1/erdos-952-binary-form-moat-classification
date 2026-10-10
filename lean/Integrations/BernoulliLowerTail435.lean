import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def trialIndicator {Ω : Type*} (E : Set Ω) : Ω → ℝ :=
  E.indicator (fun _ => 1)

noncomputable def trialCount {Ω ι : Type*} (E : ι → Set Ω) (s : Finset ι) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, trialIndicator (E i) ω

theorem measurable_trialIndicator {Ω : Type*} [MeasurableSpace Ω]
    (E : Set Ω) (hE : MeasurableSet E) : Measurable (trialIndicator E) :=
  measurable_const.indicator hE

theorem integrable_trialIndicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (hE : MeasurableSet E) :
    Integrable (trialIndicator E) μ :=
  (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator hE

/-- Exact one-trial exponential moment; no binomial random variable is needed. -/
theorem mgf_trialIndicator_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) (t : ℝ) :
    mgf (trialIndicator E) μ t = 1 + (Real.exp t - 1) * μ.real E := by
  classical
  have he : (fun ω => Real.exp (t * trialIndicator E ω)) =
      (fun ω => 1 + (Real.exp t - 1) * trialIndicator E ω) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [trialIndicator, Set.indicator, h]
  have hi := integrable_trialIndicator μ E hE
  have hm : (∫ ω, trialIndicator E ω ∂μ) = μ.real E := by
    simpa only [trialIndicator, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := μ) (1 : ℝ) hE
  rw [mgf, he, integral_add (integrable_const (1 : ℝ)) (hi.const_mul _),
    integral_const_mul, hm]
  simp

theorem mgf_trialIndicator_le_of_probability_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (q t : ℝ) (ht : 0 ≤ t) (hfloor : q ≤ μ.real E) :
    mgf (trialIndicator E) μ (-t) ≤ Real.exp (q * (Real.exp (-t) - 1)) := by
  rw [mgf_trialIndicator_eq μ E hE]
  have hc : Real.exp (-t) - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  calc
    _ ≤ 1 + q * (Real.exp (-t) - 1) := by
      have h := mul_le_mul_of_nonpos_left hfloor hc
      linarith only [h]
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (q * (Real.exp (-t) - 1))

theorem trialCount_nonneg {Ω ι : Type*} (E : ι → Set Ω) (s : Finset ι) (ω : Ω) :
    0 ≤ trialCount E s ω := by
  apply Finset.sum_nonneg
  intro i _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem measurable_trialCount {Ω ι : Type*} [MeasurableSpace Ω]
    (E : ι → Set Ω) (s : Finset ι) (hE : ∀ i, MeasurableSet (E i)) :
    Measurable (trialCount E s) :=
  Finset.measurable_sum s (fun i _ => measurable_trialIndicator (E i) (hE i))

theorem integrable_exp_neg_trialCount {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω) (s : Finset ι)
    (hE : ∀ i, MeasurableSet (E i)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * trialCount E s ω)) μ := by
  apply Integrable.of_bound
    (((measurable_trialCount E s hE).const_mul (-t)).exp.aestronglyMeasurable) 1
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (trialCount_nonneg E s ω)

/-- Independent, possibly non-identically distributed indicators with a common
hit floor. Independence is under exactly the measure supplied to this theorem. -/
theorem mgf_trialCount_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ι → Set Ω) (s : Finset ι)
    (hE : ∀ i, MeasurableSet (E i)) (hI : iIndepFun (fun i => trialIndicator (E i)) μ)
    (q t : ℝ) (ht : 0 ≤ t) (hfloor : ∀ i ∈ s, q ≤ μ.real (E i)) :
    mgf (trialCount E s) μ (-t) ≤
      Real.exp ((s.card : ℝ) * q * (Real.exp (-t) - 1)) := by
  classical
  have hm := hI.mgf_sum (fun i => measurable_trialIndicator (E i) (hE i)) s (t := -t)
  have he : (∑ i ∈ s, trialIndicator (E i)) = trialCount E s := by
    ext ω
    simp [trialCount]
  rw [he] at hm
  rw [hm]
  calc
    _ ≤ ∏ i ∈ s, Real.exp (q * (Real.exp (-t) - 1)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => mgf_nonneg)
      exact fun i hi => mgf_trialIndicator_le_of_probability_floor μ (E i) (hE i) q t ht (hfloor i hi)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [mul_assoc]

/-- A one-derivative proof of the negative-exponential quadratic upper bound.
The derivative is nonnegative by the ordinary exponential tangent inequality. -/
theorem exp_neg_le_quadratic (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  let f := fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd : ∀ x, HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    intro x
    convert (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub ((hasDerivAt_id x).neg.exp) using 1
    · rfl
    · change -1 + x + Real.exp (-x) =
        0 - 1 + 2 * x ^ (2 - 1) * 1 / 2 - Real.exp (-x) * (-1)
      ring
  have hm : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x _
    rw [(hd x).deriv]
    have h := Real.add_one_le_exp (-x)
    linarith only [h]
  have h := hm (by simp) ht ht
  dsimp [f] at h
  rw [neg_zero, Real.exp_zero] at h
  nlinarith only [h]

/-- Multiplicative Chernoff lower tail with the source's factor 1/2.
No identical-law or unconditional-after-conditioning assumption is hidden. -/
theorem measure_trialCount_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ι → Set Ω) (s : Finset ι)
    (hE : ∀ i, MeasurableSet (E i)) (hI : iIndepFun (fun i => trialIndicator (E i)) μ)
    (q v : ℝ) (hq : 0 ≤ q) (hv : 0 ≤ v) (hfloor : ∀ i ∈ s, q ≤ μ.real (E i)) :
    μ.real {ω | trialCount E s ω ≤ (1 - v) * (s.card : ℝ) * q} ≤
      Real.exp (-(s.card : ℝ) * q * v ^ 2 / 2) := by
  have hm := mgf_trialCount_le μ E s hE hI q v hv hfloor
  have ht := measure_le_le_exp_mul_mgf ((1 - v) * (s.card : ℝ) * q)
    (neg_nonpos.mpr hv) (integrable_exp_neg_trialCount μ E s hE v hv)
  calc
    _ ≤ Real.exp (-(-v) * ((1 - v) * (s.card : ℝ) * q)) * mgf (trialCount E s) μ (-v) := ht
    _ ≤ Real.exp (-(-v) * ((1 - v) * (s.card : ℝ) * q)) *
        Real.exp ((s.card : ℝ) * q * (Real.exp (-v) - 1)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (((s.card : ℝ) * q) * (v * (1 - v) + Real.exp (-v) - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_neg_le_quadratic v hv)
        (mul_nonneg (Nat.cast_nonneg s.card) hq)
      nlinarith only [h]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.measurable_trialIndicator
#print axioms BinaryFormMoat.EntropyIntegration.integrable_trialIndicator
#print axioms BinaryFormMoat.EntropyIntegration.mgf_trialIndicator_eq
#print axioms BinaryFormMoat.EntropyIntegration.mgf_trialIndicator_le_of_probability_floor
#print axioms BinaryFormMoat.EntropyIntegration.trialCount_nonneg
#print axioms BinaryFormMoat.EntropyIntegration.measurable_trialCount
#print axioms BinaryFormMoat.EntropyIntegration.integrable_exp_neg_trialCount
#print axioms BinaryFormMoat.EntropyIntegration.mgf_trialCount_le
#print axioms BinaryFormMoat.EntropyIntegration.exp_neg_le_quadratic
#print axioms BinaryFormMoat.EntropyIntegration.measure_trialCount_lower_tail
