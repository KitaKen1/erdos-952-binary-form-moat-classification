import Integrations.ContinuationResampling435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Original
variable {A H J : Type*} [Fintype A] [Fintype H] [Fintype J]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)

/-- Displacement posterior of the original joint law. A zero-weight branch
is filled with a Dirac law so every branch can be sampled; its value cancels. -/
noncomputable def originalContinuationLaw (a : A) : Measure H :=
  if θ (Prod.fst ⁻¹' {a}) = 0 then Measure.dirac h₀
  else (θ[|Prod.fst ⁻¹' {a}]).map Prod.snd

instance originalContinuationLaw_isProbabilityMeasure (a : A) :
    IsProbabilityMeasure (originalContinuationLaw θ h₀ a) := by
  unfold originalContinuationLaw
  split_ifs with ha
  · infer_instance
  · have := cond_isProbabilityMeasure (μ := θ) ha
    infer_instance

/-- Repeated independent continuations are constructed from the original
joint law, rather than merely hypothesized to have its one-trial marginal. -/
noncomputable def originalResamplingLaw : Measure (A × (J → H)) :=
  continuationResamplingLaw (θ.map Prod.fst) (originalContinuationLaw θ h₀)

theorem originalContinuationLaw_one_trial :
    continuationOneTrialLaw (θ.map Prod.fst) (originalContinuationLaw θ h₀) = θ := by
  classical
  calc
    _ = ∑ a, θ (Prod.fst ⁻¹' {a}) • θ[|Prod.fst ⁻¹' {a}] := by
      unfold continuationOneTrialLaw
      apply Finset.sum_congr rfl
      intro a _
      rw [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
      by_cases ha : θ (Prod.fst ⁻¹' {a}) = 0
      · simp [ha]
      · simp only [originalContinuationLaw, ite_eq_right ha]
        congr 1
        rw [Measure.map_map (measurable_of_finite (Prod.mk a)) measurable_snd]
        have he : Prod.mk a ∘ Prod.snd =ᵐ[θ[|Prod.fst ⁻¹' {a}]] id := by
          filter_upwards [ae_cond_mem (μ := θ) (measurable_fst (MeasurableSet.singleton a))] with ω hω
          have h : ω.1 = a := hω
          simp [← h]
        rw [Measure.map_congr he, Measure.map_id]
    _ = θ := sum_meas_smul_cond_fiber measurable_fst θ

theorem originalResamplingLaw_one_trial_map (j : J) :
    (originalResamplingLaw (J := J) θ h₀).map (fun ω => (ω.1, ω.2 j)) = θ := by
  exact (continuationResamplingLaw_one_trial_map (θ.map Prod.fst)
    (originalContinuationLaw θ h₀) j).trans (originalContinuationLaw_one_trial θ h₀)

theorem originalResamplingLaw_identDistrib {G : Type*} [MeasurableSpace G]
    (f : A × H → G) (j : J) :
    IdentDistrib (fun ω : A × (J → H) => f (ω.1, ω.2 j)) f
      (originalResamplingLaw θ h₀) θ := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  rw [show (fun ω : A × (J → H) => f (ω.1, ω.2 j)) =
    f ∘ (fun ω : A × (J → H) => (ω.1, ω.2 j)) from rfl,
    ← Measure.map_map (measurable_of_finite f) (measurable_of_finite _),
    originalResamplingLaw_one_trial_map θ h₀ j]

theorem originalResamplingLaw_cond_projected_trial_map {G : Type*} [MeasurableSpace G]
    (φ : H → G) (a : A) (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (j : J) :
    ((originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]).map
      (fun ω => φ (ω.2 j)) = (originalContinuationLaw θ h₀ a).map φ := by
  have ha' : (θ.map Prod.fst) {a} ≠ 0 := by
    rwa [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
  rw [show (fun ω : A × (J → H) => φ (ω.2 j)) = φ ∘ (fun ω => ω.2 j) from rfl,
    ← Measure.map_map (measurable_of_finite φ) (measurable_of_finite _)]
  congr 1
  exact continuationResamplingLaw_cond_trial_map (θ.map Prod.fst)
    (originalContinuationLaw θ h₀) a ha' j

theorem originalResamplingLaw_cond_projected_iIndepFun {G : Type*} [MeasurableSpace G]
    (φ : H → G) (a : A) (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) :
    iIndepFun (fun j (ω : A × (J → H)) => φ (ω.2 j))
      ((originalResamplingLaw θ h₀)[|Prod.fst ⁻¹' {a}]) := by
  have ha' : (θ.map Prod.fst) {a} ≠ 0 := by
    rwa [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
  exact (continuationResamplingLaw_cond_iIndepFun (J := J) (θ.map Prod.fst)
    (originalContinuationLaw θ h₀) a ha').comp (fun _ => φ) (fun _ => measurable_of_finite φ)

omit [IsProbabilityMeasure θ] in
theorem originalContinuationLaw_cond_identDistrib {G : Type*} [MeasurableSpace G]
    (f : A × H → G) (a : A) (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) :
    IdentDistrib (fun h => f (a, h)) f (originalContinuationLaw θ h₀ a)
      (θ[|Prod.fst ⁻¹' {a}]) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  simp only [originalContinuationLaw, ite_eq_right ha]
  rw [Measure.map_map (measurable_of_finite _) measurable_snd]
  apply Measure.map_congr
  filter_upwards [ae_cond_mem (μ := θ) (measurable_fst (MeasurableSet.singleton a))] with ω hω
  have h : ω.1 = a := hω
  simp [← h]

end Original
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.originalContinuationLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.originalContinuationLaw_one_trial
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_one_trial_map
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_projected_trial_map
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_projected_iIndepFun
#print axioms BinaryFormMoat.EntropyIntegration.originalContinuationLaw_cond_identDistrib
