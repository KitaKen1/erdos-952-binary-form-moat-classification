import Integrations.OneStepCoverage435
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Pi

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Finite
variable {A H J : Type*} [Fintype A] [Fintype H] [Fintype J]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (ρ : Measure A) [IsProbabilityMeasure ρ] (ν : A → Measure H)
  [∀ a, IsProbabilityMeasure (ν a)]

/-- First sample the exact mixing value, then independently resample its
continuations. Coordinates are not asserted independent before conditioning. -/
noncomputable def continuationResamplingLaw : Measure (A × (J → H)) :=
  ∑ a, ρ {a} • (Measure.pi (fun _ : J => ν a)).map (Prod.mk a)

noncomputable def continuationOneTrialLaw : Measure (A × H) :=
  ∑ a, ρ {a} • (ν a).map (Prod.mk a)

omit [IsProbabilityMeasure ρ] [∀ a, IsProbabilityMeasure (ν a)] in
theorem continuationResamplingLaw_apply (E : Set (A × (J → H))) :
    continuationResamplingLaw (J := J) ρ ν E =
      ∑ a, ρ {a} * Measure.pi (fun _ : J => ν a) ((Prod.mk a) ⁻¹' E) := by
  simp only [continuationResamplingLaw, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet]

instance continuationResamplingLaw_isProbabilityMeasure :
    IsProbabilityMeasure (continuationResamplingLaw (J := J) ρ ν) := by
  constructor
  rw [continuationResamplingLaw_apply]
  simp only [Set.preimage_univ, measure_univ, mul_one]
  simp

omit [IsProbabilityMeasure ρ] [∀ a, IsProbabilityMeasure (ν a)] in
theorem continuationResamplingLaw_fiber_inter (a : A) (E : Set (A × (J → H))) :
    continuationResamplingLaw (J := J) ρ ν (Prod.fst ⁻¹' {a} ∩ E) =
      ρ {a} * Measure.pi (fun _ : J => ν a) ((Prod.mk a) ⁻¹' E) := by
  classical
  rw [continuationResamplingLaw_apply]
  rw [Finset.sum_eq_single a]
  · congr 2
    ext h
    simp
  · intro b _ hba
    have he : (Prod.mk b) ⁻¹' (Prod.fst ⁻¹' {a} ∩ E) = (∅ : Set (J → H)) := by
      ext h
      simp [hba]
    simp [he]
  · simp

omit [IsProbabilityMeasure ρ] in
theorem continuationResamplingLaw_fiber (a : A) :
    continuationResamplingLaw (J := J) ρ ν (Prod.fst ⁻¹' {a}) = ρ {a} := by
  simpa using continuationResamplingLaw_fiber_inter (J := J) ρ ν a Set.univ

theorem continuationResamplingLaw_cond_fiber (a : A) (ha : ρ {a} ≠ 0) :
    (continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}] =
      (Measure.pi (fun _ : J => ν a)).map (Prod.mk a) := by
  ext E hE
  rw [cond_apply (measurable_fst (MeasurableSet.singleton a)),
    continuationResamplingLaw_fiber, continuationResamplingLaw_fiber_inter,
    Measure.map_apply (measurable_of_finite _) hE, ← mul_assoc,
    ENNReal.inv_mul_cancel ha (measure_ne_top ρ {a}), one_mul]

omit [IsProbabilityMeasure ρ] in
theorem continuationResamplingLaw_cond_zero_fiber (a : A) (ha : ρ {a} = 0) :
    (continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}] = 0 := by
  apply cond_eq_zero_of_meas_eq_zero
  rw [continuationResamplingLaw_fiber, ha]

theorem continuationResamplingLaw_cond_data_map (a : A) (ha : ρ {a} ≠ 0) :
    ((continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}]).map Prod.snd =
      Measure.pi (fun _ : J => ν a) := by
  rw [continuationResamplingLaw_cond_fiber ρ ν a ha,
    Measure.map_map measurable_snd (measurable_of_finite _)]
  simp only [Function.comp_def, Measure.map_id']

theorem continuationResamplingLaw_cond_trial_map (a : A) (ha : ρ {a} ≠ 0) (j : J) :
    ((continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}]).map
      (fun ω => ω.2 j) = ν a := by
  rw [show (fun ω : A × (J → H) => ω.2 j) = Function.eval j ∘ Prod.snd from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_snd,
    continuationResamplingLaw_cond_data_map ρ ν a ha]
  exact (measurePreserving_eval (fun _ : J => ν a) j).map_eq

theorem continuationResamplingLaw_cond_iIndepFun (a : A) (ha : ρ {a} ≠ 0) :
    iIndepFun (fun j (ω : A × (J → H)) => ω.2 j)
      ((continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}]) := by
  have := cond_isProbabilityMeasure (μ := continuationResamplingLaw (J := J) ρ ν)
    (s := Prod.fst ⁻¹' {a})
    (by simpa only [continuationResamplingLaw_fiber] using ha)
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun j =>
    ((measurable_pi_apply j).comp measurable_snd).aemeasurable)).mpr
  change ((continuationResamplingLaw (J := J) ρ ν)[|Prod.fst ⁻¹' {a}]).map Prod.snd = _
  rw [continuationResamplingLaw_cond_data_map ρ ν a ha]
  congr 1
  funext j
  exact (continuationResamplingLaw_cond_trial_map ρ ν a ha j).symm

omit [IsProbabilityMeasure ρ] in
theorem continuationResamplingLaw_one_trial_map (j : J) :
    (continuationResamplingLaw (J := J) ρ ν).map (fun ω => (ω.1, ω.2 j)) =
      continuationOneTrialLaw ρ ν := by
  ext E hE
  rw [Measure.map_apply (measurable_of_finite _) hE, continuationResamplingLaw_apply]
  simp only [continuationOneTrialLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have hm : (Measure.pi (fun _ : J => ν a)).map (fun h => (a, h j)) =
      (ν a).map (Prod.mk a) := by
    exact (Measure.map_map (μ := Measure.pi (fun _ : J => ν a))
      (measurable_of_finite (Prod.mk a)) (measurable_of_finite (fun h : J → H => h j))).symm.trans
      (congrArg (fun m : Measure H => m.map (Prod.mk a))
        (measurePreserving_eval (fun _ : J => ν a) j).map_eq)
  have h := congrArg (fun m : Measure (A × H) => m E) hm
  rw [Measure.map_apply (measurable_of_finite _) hE] at h
  exact h

omit [IsProbabilityMeasure ρ] in
theorem continuationResamplingLaw_identDistrib_trials (j k : J) :
    IdentDistrib (fun ω : A × (J → H) => (ω.1, ω.2 j))
      (fun ω => (ω.1, ω.2 k)) (continuationResamplingLaw ρ ν) (continuationResamplingLaw ρ ν) := by
  exact ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable,
    (continuationResamplingLaw_one_trial_map ρ ν j).trans
      (continuationResamplingLaw_one_trial_map ρ ν k).symm⟩

end Finite
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_apply
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_fiber_inter
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_fiber
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_cond_fiber
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_cond_zero_fiber
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_cond_data_map
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_cond_trial_map
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_cond_iIndepFun
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_one_trial_map
#print axioms BinaryFormMoat.EntropyIntegration.continuationResamplingLaw_identDistrib_trials
