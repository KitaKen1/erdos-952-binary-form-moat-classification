import Integrations.PassingLists435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Original
variable {A H J C : Type*} [Fintype A] [Fintype H] [Fintype J] [Fintype C]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)

omit [Fintype C] in
theorem originalResamplingLaw_cond_data_map (a : A) (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) :
    ((originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]).map Prod.snd =
      Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a) := by
  have ha' : (θ.map Prod.fst) {a} ≠ 0 := by
    rwa [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
  exact continuationResamplingLaw_cond_data_map (θ.map Prod.fst)
    (originalContinuationLaw θ h₀) a ha'

/-- A passing list computed from posterior packages is evaluated under the
exact earlier fiber of the constructed resampling law. -/
theorem originalResamplingLaw_cond_passingList_probability (a : A)
    (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (reject : C → H → Prop) (x : C) :
    ((originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]).real
      {ω | x ∈ passingList reject ω.2} =
      ((originalContinuationLaw θ h₀ a).real {h | ¬ reject x h}) ^ Fintype.card J := by
  have hm := originalResamplingLaw_cond_data_map (J := J) θ h₀ a ha
  have he := congrArg (fun m => m.real {h | x ∈ passingList reject h}) hm
  rw [map_measureReal_apply measurable_snd (Set.toFinite _).measurableSet] at he
  exact he.trans (passingList_survival_probability _ reject x)

theorem originalResamplingLaw_cond_passingList_exp_bound (a : A)
    (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (reject : C → H → Prop) (x : C) (ε : ℝ)
    (hε : ε ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h}) :
    ((originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]).real
      {ω | x ∈ passingList reject ω.2} ≤ Real.exp (-(Fintype.card J : ℝ) * ε) := by
  have hm := originalResamplingLaw_cond_data_map (J := J) θ h₀ a ha
  have he := congrArg (fun m => m.real {h | x ∈ passingList reject h}) hm
  rw [map_measureReal_apply measurable_snd (Set.toFinite _).measurableSet] at he
  exact he.le.trans (passingList_survival_exp_bound (J := J) _ reject x ε hε)

theorem originalResamplingLaw_cond_passingList_integral (a : A)
    (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (reject : C → H → Prop) :
    (∫ ω, ((passingList reject ω.2).card : ℝ)
      ∂(originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]) =
      ∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a) := by
  rw [← originalResamplingLaw_cond_data_map (J := J) θ h₀ a ha,
    integral_map measurable_snd.aemeasurable
      (measurable_of_finite (fun h : J → H => ((passingList reject h).card : ℝ))).aestronglyMeasurable]

theorem originalResamplingLaw_cond_expected_passingList_card_le (a : A)
    (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (reject : C → H → Prop) (B : Finset C) (ε : ℝ)
    (hfloor : ∀ x ∉ B, ε ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h}) :
    (∫ ω, ((passingList reject ω.2).card : ℝ)
      ∂(originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]) ≤
      (B.card : ℝ) + Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε) := by
  rw [originalResamplingLaw_cond_passingList_integral θ h₀ a ha reject]
  exact expected_passingList_card_le _ reject B ε hfloor

theorem originalResamplingLaw_cond_passingList_source_bound (a : A)
    (ha : θ (Prod.fst ⁻¹' {a}) ≠ 0) (reject : C → H → Prop) (B : Finset C) (ε M : ℝ)
    (hfloor : ∀ x ∉ B, ε ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : (B.card : ℝ) ≤ 4 * M)
    (ht : Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε) ≤ M) :
    (∫ ω, ((passingList reject ω.2).card : ℝ)
      ∂(originalResamplingLaw (J := J) θ h₀)[|Prod.fst ⁻¹' {a}]) ≤ 5 * M := by
  rw [originalResamplingLaw_cond_passingList_integral θ h₀ a ha reject]
  exact expected_passingList_card_source_bound _ reject B ε M hfloor hB ht

theorem originalResamplingLaw_passingList_integral_eq_sum (reject : C → H → Prop) :
    (∫ ω, ((passingList reject ω.2).card : ℝ) ∂originalResamplingLaw (J := J) θ h₀) =
      ∑ a, (θ.map Prod.fst).real {a} *
        (∫ h : J → H, ((passingList reject h).card : ℝ)
          ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) := by
  rw [originalResamplingLaw, continuationResamplingLaw,
    integral_finsetSum_measure (fun _ _ =>
      Integrable.of_finite.smul_measure (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_smul_measure, integral_map (measurable_of_finite (Prod.mk a)).aemeasurable
    (measurable_of_finite (fun ω : A × (J → H) => ((passingList reject ω.2).card : ℝ))).aestronglyMeasurable]
  rfl

/-- Uniform positive-fiber bounds average back to the original experiment;
zero-weight filler branches contribute exactly zero. -/
theorem originalResamplingLaw_expected_passingList_source_bound (reject : C → H → Prop)
    (B : A → Finset C) (ε : A → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M) :
    (∫ ω, ((passingList reject ω.2).card : ℝ) ∂originalResamplingLaw (J := J) θ h₀) ≤
      5 * M := by
  rw [originalResamplingLaw_passingList_integral_eq_sum θ h₀ reject]
  have hw : ∑ a, (θ.map Prod.fst).real {a} = 1 := by
    simp
  calc
    _ ≤ ∑ a, (θ.map Prod.fst).real {a} * (5 * M) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : θ (Prod.fst ⁻¹' {a}) = 0
      · simp [measureReal_def, Measure.map_apply measurable_fst (MeasurableSet.singleton a), ha]
      · exact mul_le_mul_of_nonneg_left
          (expected_passingList_card_source_bound _ reject (B a) (ε a) M
            (hfloor a ha) (hB a ha) (ht a ha)) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, hw, one_mul]

end Original
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_data_map
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_passingList_probability
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_passingList_exp_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_passingList_integral
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_expected_passingList_card_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_cond_passingList_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_integral_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_expected_passingList_source_bound
