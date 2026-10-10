import Moat.UniformSampling
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BinaryFormMoat

/-- Hoeffding's bound with a deterministic upper bound on the mean.
The law, independence, ranges, and mean bound all refer to the same measure. -/
theorem bounded_independent_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) (s : Finset ι)
    (w : ι → ℝ) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 (w i))
    (M : ℝ) (hmean : (∑ i ∈ s, ∫ ω, X i ω ∂μ) ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | M + t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-2 * t ^ 2 / (∑ i ∈ s, (w i) ^ 2)) := by
  have hcenter : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ :=
    hindep.comp (fun i x => x - ∫ ω, X i ω ∂μ) (fun _ => by fun_prop)
  have hsub : ∀ i ∈ s, HasSubgaussianMGF
      (fun ω => X i ω - ∫ x, X i x ∂μ) ((‖w i‖₊ / 2) ^ 2) μ := by
    intro i hi
    simpa only [sub_zero] using
      hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable (hbound i hi)
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenter hsub ht
  have hden : (2 * ∑ i ∈ s, (((‖w i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) =
      (∑ i ∈ s, (w i) ^ 2) / 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, div_pow, sq_abs]
    rw [← Finset.sum_div]
    ring
  simp only [NNReal.coe_sum] at htail
  rw [hden] at htail
  have hexp : -t ^ 2 / ((∑ i ∈ s, (w i) ^ 2) / 2) =
      -2 * t ^ 2 / (∑ i ∈ s, (w i) ^ 2) := by ring
  rw [hexp] at htail
  apply le_trans (measureReal_mono ?_) htail
  intro ω hω
  change M + t ≤ ∑ i ∈ s, X i ω at hω
  simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
  linarith

/-- An explicit finite counting version of Hoeffding for a box of independent
coordinate choices. The average and event fraction use exactly the same box. -/
theorem box_upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (S : ∀ i, Finset (K i))
    (hS : ∀ i, (S i).Nonempty) (g : ∀ i, K i → ℝ) (w : ι → ℝ)
    (hbound : ∀ i x, g i x ∈ Set.Icc 0 (w i)) (M : ℝ)
    (hmean : (∑ σ ∈ Fintype.piFinset S, ∑ i, g i (σ i)) /
      (Fintype.piFinset S).card ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    (((Fintype.piFinset S).filter (fun σ => M + t ≤ ∑ i, g i (σ i))).card : ℝ) /
      (Fintype.piFinset S).card ≤ Real.exp (-2 * t ^ 2 / (∑ i, (w i) ^ 2)) := by
  classical
  let μ := uniformOn (Fintype.piFinset S : Set (∀ i, K i))
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn
    (Fintype.piFinset S).finite_toSet (Fintype.piFinset_nonempty.mpr hS)
  have hmean' : (∑ i, ∫ σ, g i (σ i) ∂μ) ≤ M := by
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    exact (integral_uniformOn_finset _ _).trans_le hmean
  have htail := bounded_independent_upper_tail μ (fun i σ => g i (σ i))
    (fun _ => by measurability) (iIndepFun_uniformOn_box S hS g) Finset.univ w
    (fun i _ => Filter.Eventually.of_forall fun σ => hbound i (σ i)) M hmean' t ht
  rw [uniformOn_real_event] at htail
  exact htail

end BinaryFormMoat
