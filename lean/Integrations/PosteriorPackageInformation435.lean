import Integrations.InformationTransport435
import Integrations.ExpectedListEntropy435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Original
variable {A H J : Type*} [Fintype A] [Fintype H] [Fintype J]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)

theorem originalResamplingLaw_fiber_matches_original (a : A) :
    originalResamplingLaw (J := J) θ h₀ (Prod.fst ⁻¹' {a}) = θ (Prod.fst ⁻¹' {a}) := by
  unfold originalResamplingLaw
  rw [continuationResamplingLaw_fiber, Measure.map_apply measurable_fst
    (MeasurableSet.singleton a)]

theorem originalResamplingLaw_one_package_condMutualInfo {C K U : Type*}
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (X : A → C) (Y : A × H → K) (O : A → U) (j : J) :
    condMutualInfo (fun ω : A × (J → H) => X ω.1)
      (fun ω => Y (ω.1, ω.2 j)) (fun ω => O ω.1) (originalResamplingLaw θ h₀) =
    condMutualInfo (fun ω : A × H => X ω.1) Y (fun ω => O ω.1) θ := by
  classical
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  exact condMutualInfo_eq_of_identDistrib _ θ _ _ _ _ _ _
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (originalResamplingLaw_identDistrib θ h₀
      (fun ω : A × H => (X ω.1, (Y ω, O ω.1))) j)

end Original

section ExactPair
variable {C U H J : Type*} [Fintype C] [Fintype U] [Fintype H] [Fintype J]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure ((C × U) × H)) [IsProbabilityMeasure θ] (h₀ : H)

/-- Resample conditional on precisely (X,O). A finer-checkpoint independent
law is not silently reused for this subadditivity inequality. -/
theorem originalResamplingLaw_package_condMutualInfo_le :
    condMutualInfo (fun ω : (C × U) × (J → H) => ω.1.1) Prod.snd
      (fun ω => ω.1.2) (originalResamplingLaw θ h₀) ≤
    (Fintype.card J : ℝ) * condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd
      (fun ω => ω.1.2) θ := by
  classical
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  have hI (a : C × U)
      (ha : (originalResamplingLaw (J := J) θ h₀) ((fun ω => (ω.1.1, ω.1.2)) ⁻¹' {a}) ≠ 0) :
      iIndepFun (fun j (ω : (C × U) × (J → H)) => ω.2 j)
        ((originalResamplingLaw θ h₀)[|(fun ω => (ω.1.1, ω.1.2)) ⁻¹' {a}]) := by
    change (originalResamplingLaw (J := J) θ h₀) (Prod.fst ⁻¹' {a}) ≠ 0 at ha
    rw [originalResamplingLaw_fiber_matches_original] at ha
    exact originalResamplingLaw_cond_projected_iIndepFun θ h₀ id a ha
  have h := condMutualInfo_pi_le_sum_of_fiber_independence
    (originalResamplingLaw (J := J) θ h₀) (fun ω => ω.1.1) (fun ω => ω.1.2)
    (fun j ω => ω.2 j) (measurable_of_finite _) (measurable_of_finite _)
    (fun _ => measurable_of_finite _) hI
  simp_rw [originalResamplingLaw_one_package_condMutualInfo θ h₀ Prod.fst Prod.snd Prod.snd] at h
  simpa using h

theorem originalResamplingLaw_one_package_lower_from_budget (j : J) (ℓ : ℝ)
    (hbudget : ℓ ≤ condMutualInfo (fun ω : (C × U) × (J → H) => ω.1.1) Prod.snd
      (fun ω => ω.1.2) (originalResamplingLaw θ h₀)) :
    ℓ / Fintype.card J ≤ condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd
      (fun ω => ω.1.2) θ := by
  have hm : (0 : ℝ) < Fintype.card J := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
  apply (div_le_iff₀ hm).mpr
  have h := hbudget.trans (originalResamplingLaw_package_condMutualInfo_le θ h₀)
  simpa only [mul_comm] using h

theorem originalResamplingLaw_passingList_one_package_lower_bound (j : J)
    (reject : C → H → Prop) (B : C × U → Finset C) (ε : C × U → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀, ω.1.1 ∈ passingList reject ω.2) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      Real.log (1 + 5 * M)) / Fintype.card J ≤
    condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ := by
  exact originalResamplingLaw_one_package_lower_from_budget θ h₀ j _
    (originalResamplingLaw_passingList_information_lower_bound θ h₀ j Prod.fst Prod.snd
      reject B ε M hfloor hB ht hmem)

theorem originalResamplingLaw_passingList_one_package_lower_bound_error (j : J)
    (reject : C → H → Prop) (B : C × U → Finset C) (ε : C × U → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ - Real.log 2 -
      Real.log (1 + 5 * M) - (originalResamplingLaw (J := J) θ h₀).real
        {ω | ω.1.1 ∉ passingList reject ω.2} * Real.log (Fintype.card C)) / Fintype.card J ≤
    condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ := by
  exact originalResamplingLaw_one_package_lower_from_budget θ h₀ j _
    (originalResamplingLaw_passingList_information_lower_bound_error θ h₀ j Prod.fst Prod.snd
      reject B ε M hfloor hB ht)

end ExactPair
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_fiber_matches_original
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_one_package_condMutualInfo
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_package_condMutualInfo_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_one_package_lower_from_budget
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_one_package_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_one_package_lower_bound_error
