import Integrations.SmoothedPassingFloors435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Finite
variable {Ω A D : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → A) (F : A → D)

omit [Fintype A] [Fintype D] in
/-- Reconditioning checkpoint data on a compatible exact time restores
the ORIGINAL exact-time law, including zero-mass fibers. -/
theorem cond_coarsening_exact_fiber (d : D) (a : A) (ha : F a = d) :
    (μ[|(F ∘ σ) ⁻¹' {d}])[|σ ⁻¹' {a}] = μ[|σ ⁻¹' {a}] := by
  rw [cond_cond_eq_cond_inter ((measurable_of_finite _) (MeasurableSet.singleton d))
    ((measurable_of_finite _) (MeasurableSet.singleton a)) μ]
  congr 1
  apply Set.inter_eq_right.mpr
  intro ω hω
  change F (σ ω) = d
  change σ ω = a at hω
  simpa only [hω] using ha

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype D]
  [IsProbabilityMeasure μ] in
/-- Incompatible exact times have ZERO posterior mass. No probability
instance is required on such branches. -/
theorem coarsening_incompatible_fiber_zero (d : D) (a : A) (ha : F a ≠ d) :
    (μ[|(F ∘ σ) ⁻¹' {d}]).real (σ ⁻¹' {a}) = 0 := by
  have he : (F ∘ σ) ⁻¹' {d} ∩ σ ⁻¹' {a} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hσ : σ ω = a := hω.2
    have hF : F (σ ω) = d := hω.1
    exact ha (by simpa only [hσ] using hF)
  simp only [measureReal_def, cond_apply ((measurable_of_finite _) (MeasurableSet.singleton d)),
    he, measure_empty, mul_zero, ENNReal.toReal_zero]

omit [Fintype D] in
/-- The EXACT posterior-kernel mixture for checkpoint residue data F(sigma).
Fresh exact-time laws are not changed by coarser residue conditioning. -/
theorem coarsening_exact_fiber_mixture (d : D) (E : Set Ω) :
    fiberConditionalReal μ (F ∘ σ) d E = ∑ a,
      (μ[|(F ∘ σ) ⁻¹' {d}]).real (σ ⁻¹' {a}) * fiberConditionalReal μ σ a E := by
  by_cases hd : μ ((F ∘ σ) ⁻¹' {d}) = 0
  · simp [fiberConditionalReal, cond_eq_zero_of_meas_eq_zero hd]
  · let : IsProbabilityMeasure (μ[|(F ∘ σ) ⁻¹' {d}]) := cond_isProbabilityMeasure hd
    unfold fiberConditionalReal
    rw [measureReal_eq_sum_fiberConditionalReal (μ[|(F ∘ σ) ⁻¹' {d}]) σ
      (measurable_of_finite _) E (Set.toFinite _).measurableSet]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : F a = d
    · rw [fiberConditionalReal, cond_coarsening_exact_fiber μ σ F d a ha]
    · rw [coarsening_incompatible_fiber_zero μ σ F d a ha, zero_mul, zero_mul]

omit [Fintype D] in
/-- Compatible good exact-time floors mix to the ACTUAL posterior event
floor. The coarse datum must be a function of the checkpoint, an explicit
condition essential for passing-list packages. -/
theorem coarsening_good_exact_floor (d : D) (hd : μ ((F ∘ σ) ⁻¹' {d}) ≠ 0)
    (E : Set Ω) (good : Finset A) (δ u : ℝ) (hδ : 0 ≤ δ)
    (hgood : u ≤ (μ[|(F ∘ σ) ⁻¹' {d}]).real (σ ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, μ (σ ⁻¹' {a}) ≠ 0 → F a = d → δ ≤ fiberConditionalReal μ σ a E) :
    δ * u ≤ fiberConditionalReal μ (F ∘ σ) d E := by
  let : IsProbabilityMeasure (μ[|(F ∘ σ) ⁻¹' {d}]) := cond_isProbabilityMeasure hd
  have hf := measureReal_ge_good_fiber_floor (μ[|(F ∘ σ) ⁻¹' {d}]) σ (measurable_of_finite _)
    E (Set.toFinite _).measurableSet good δ (by
      intro a ha hmass
      have hmatch : F a = d := by
        by_contra hn
        have hzero := coarsening_incompatible_fiber_zero μ σ F d a hn
        exact hmass (((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _))
      have hprior : μ (σ ⁻¹' {a}) ≠ 0 := by
        intro hz
        have he : μ ((F ∘ σ) ⁻¹' {d} ∩ σ ⁻¹' {a}) = 0 := measure_mono_null Set.inter_subset_right hz
        have hzero : (μ[|(F ∘ σ) ⁻¹' {d}]) (σ ⁻¹' {a}) = 0 := by
          rw [cond_apply ((measurable_of_finite _) (MeasurableSet.singleton d)), he, mul_zero]
        exact hmass hzero
      rw [fiberConditionalReal, cond_coarsening_exact_fiber μ σ F d a hmatch]
      exact hfloor a ha hprior hmatch)
  exact (mul_le_mul_of_nonneg_left hgood hδ).trans hf

end Finite
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.cond_coarsening_exact_fiber
#print axioms BinaryFormMoat.EntropyIntegration.coarsening_incompatible_fiber_zero
#print axioms BinaryFormMoat.EntropyIntegration.coarsening_exact_fiber_mixture
#print axioms BinaryFormMoat.EntropyIntegration.coarsening_good_exact_floor
