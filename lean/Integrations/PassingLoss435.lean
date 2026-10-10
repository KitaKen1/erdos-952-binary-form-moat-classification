import Integrations.PosteriorPackageInformation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem not_mem_passingList_iff {C H J : Type*} [Fintype C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) (x : C) :
    x ∉ passingList reject h ↔ ∃ j, reject x (h j) := by
  classical
  simp [mem_passingList]

/-- True-value loss needs only a union bound, not trial independence. -/
theorem passingList_loss_probability_le_sum {Ω C H J : Type*}
    [MeasurableSpace Ω] [Fintype C] [Fintype J]
    (μ : Measure Ω) (X : Ω → C) (D : Ω → J → H) (reject : C → H → Prop) :
    μ.real {ω | X ω ∉ passingList reject (D ω)} ≤
      ∑ j : J, μ.real {ω | reject (X ω) (D ω j)} := by
  have he : {ω | X ω ∉ passingList reject (D ω)} =
      ⋃ j : J, {ω | reject (X ω) (D ω j)} := by
    ext ω
    simp [not_mem_passingList_iff]
  rw [he]
  exact measureReal_iUnion_fintype_le _

section Original
variable {A H J C : Type*} [Fintype A] [Fintype H] [Fintype J] [Fintype C]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)

omit [Fintype C] in
/-- Preserve the joint checkpoint/package event, including its correlations. -/
theorem originalResamplingLaw_true_reject_probability (X : A → C)
    (reject : C → H → Prop) (j : J) :
    (originalResamplingLaw (J := J) θ h₀).real
      {ω | reject (X ω.1) (ω.2 j)} = θ.real {ω | reject (X ω.1) ω.2} := by
  have he := congrArg (fun μ => μ.real {ω : A × H | reject (X ω.1) ω.2})
    (originalResamplingLaw_one_trial_map θ h₀ j)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at he
  exact he

theorem originalResamplingLaw_passingList_loss_le (X : A → C) (reject : C → H → Prop) :
    (originalResamplingLaw (J := J) θ h₀).real
      {ω | X ω.1 ∉ passingList reject ω.2} ≤
      (Fintype.card J : ℝ) * θ.real {ω | reject (X ω.1) ω.2} := by
  have h := passingList_loss_probability_le_sum (originalResamplingLaw (J := J) θ h₀)
    (fun ω => X ω.1) Prod.snd reject
  simp_rw [originalResamplingLaw_true_reject_probability θ h₀ X reject] at h
  simpa using h

/-- Dividing the information budget by the package count cancels that
count in the true-value error penalty. No small total-loss premise is used. -/
theorem originalResamplingLaw_normalized_loss_le (j : J) (X : A → C)
    (reject : C → H → Prop) (c : ℝ) (hc : 0 ≤ c) :
    ((originalResamplingLaw (J := J) θ h₀).real
      {ω | X ω.1 ∉ passingList reject ω.2} * c) / Fintype.card J ≤
      θ.real {ω | reject (X ω.1) ω.2} * c := by
  have hm : (0 : ℝ) < Fintype.card J := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
  apply (div_le_iff₀ hm).mpr
  have h := mul_le_mul_of_nonneg_right
    (originalResamplingLaw_passingList_loss_le (J := J) θ h₀ X reject) hc
  convert h using 1
  ring

end Original

section ExactPair
variable {C U H J : Type*} [Fintype C] [Fintype U] [Fintype H] [Fintype J]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure ((C × U) × H)) [IsProbabilityMeasure θ] (h₀ : H)

theorem originalResamplingLaw_passingList_lower_bound_one_trial_error (j : J)
    (reject : C → H → Prop) (B : C × U → Finset C) (ε : C × U → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      Real.log 2 - Real.log (1 + 5 * M)) / Fintype.card J -
      θ.real {ω | reject ω.1.1 ω.2} * Real.log (Fintype.card C) ≤
    condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ := by
  have hl := originalResamplingLaw_passingList_one_package_lower_bound_error θ h₀ j
    reject B ε M hfloor hB ht
  have he := originalResamplingLaw_normalized_loss_le θ h₀ j Prod.fst reject
    (Real.log (Fintype.card C)) (Real.log_natCast_nonneg _)
  rw [sub_div] at hl
  linarith

theorem originalResamplingLaw_passingList_lower_bound_error_quota (j : J)
    (reject : C → H → Prop) (B : C × U → Finset C) (ε : C × U → ℝ) (M q : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M)
    (hq : θ.real {ω | reject ω.1.1 ω.2} ≤ q) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      Real.log 2 - Real.log (1 + 5 * M)) / Fintype.card J -
      q * Real.log (Fintype.card C) ≤
    condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ := by
  have hl := originalResamplingLaw_passingList_lower_bound_one_trial_error θ h₀ j
    reject B ε M hfloor hB ht
  have he := mul_le_mul_of_nonneg_right hq (Real.log_natCast_nonneg (Fintype.card C))
  linarith

end ExactPair
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.not_mem_passingList_iff
#print axioms BinaryFormMoat.EntropyIntegration.passingList_loss_probability_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_true_reject_probability
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_loss_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_normalized_loss_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_lower_bound_one_trial_error
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_lower_bound_error_quota
