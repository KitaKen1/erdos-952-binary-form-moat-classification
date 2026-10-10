import Integrations.PosteriorLogLists435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Favorable branches already pay G. An unfavorable branch costs only the
remaining gap D. Exact original weights, zero fibers and posterior Jensen
are retained; a log(card C) penalty would lose the all-degree rate margin. -/
theorem originalResamplingLaw_favorable_gap_log_budget {A H J C : Type*}
    [Fintype A] [Fintype H] [Fintype J] [Fintype C] [Nonempty C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)
    (reject : C → H → Prop) (bad : Finset A) (M G D : ℝ) (hG : Real.log (1 + M) ≤ G)
    (hC : Real.log (Fintype.card C) ≤ G + D)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M) :
    (∫ ω, passingListLog reject ω.2 ∂originalResamplingLaw (J := J) θ h₀) ≤
      G + θ.real (Prod.fst ⁻¹' (bad : Set A)) * D := by
  let w := fun a : A => (θ.map Prod.fst).real {a}
  have hw : ∑ a, w a = 1 := by simp [w]
  have hf (a : A) : w a *
      (∫ h : J → H, passingListLog reject h
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤
      w a * (G + if a ∈ bad then D else 0) := by
    by_cases ha : θ (Prod.fst ⁻¹' {a}) = 0
    · simp [w, map_measureReal_apply measurable_fst (MeasurableSet.singleton _), measureReal_def, ha]
    · apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      by_cases hb : a ∈ bad
      · simp only [hb, ite_true]
        have hc : (∫ h : J → H, passingListLog reject h
            ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ Real.log (Fintype.card C) := by
          calc
            _ ≤ ∫ _h : J → H, Real.log (Fintype.card C)
                ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a) :=
              integral_mono_ae Integrable.of_finite Integrable.of_finite
                (Filter.Eventually.of_forall (passingListLog_le_log_card reject))
            _ = _ := by simp
        exact hc.trans hC
      · simp only [hb, ite_false, add_zero]
        exact (integral_passingListLog_le _ reject M (hbudget a hb ha)).trans hG
  rw [originalResamplingLaw_integral_package]
  calc
    _ ≤ ∑ a, w a * (G + if a ∈ bad then D else 0) :=
      Finset.sum_le_sum (fun a _ => hf a)
    _ = G + (∑ a ∈ bad, w a) * D := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
      congr 1
      simp only [mul_ite, mul_zero, ← Finset.sum_filter]
      have he : Finset.univ.filter (fun a : A => a ∈ bad) = bad := by ext; simp
      rw [he, ← Finset.sum_mul]
    _ = _ := by
      have he : (∑ a ∈ bad, w a) = θ.real (Prod.fst ⁻¹' (bad : Set A)) := by
        simp only [w, map_measureReal_apply measurable_fst (MeasurableSet.singleton _)]
        exact sum_measureReal_preimage_singleton bad
          (fun a _ => measurable_fst (MeasurableSet.singleton a))
      rw [he]

/-- The favorable list cost has the same leading term as the manuscript.
The extra log 6 replaces log 5 and is a fixed threshold cost. -/
theorem root_passing_log_gap (p : ℕ) (hp : 1 ≤ p) (β : ℝ)
    (hβ₁ : β ≤ 1) :
    Real.log (1 + 5 * (p : ℝ) ^ (1 - β)) ≤ (1 - β) * Real.log p + Real.log 6 ∧
    Real.log p ≤ ((1 - β) * Real.log p + Real.log 6) + β * Real.log p := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have ha := Real.one_le_rpow hp₁ (by linarith : 0 ≤ 1 - β)
  have hl := Real.log_le_log (by positivity : 0 < 1 + 5 * (p : ℝ) ^ (1 - β))
    (by linarith : 1 + 5 * (p : ℝ) ^ (1 - β) ≤ 6 * (p : ℝ) ^ (1 - β))
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hp₀ _).ne', Real.log_rpow hp₀] at hl
  have h6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  constructor <;> linarith

section Information
variable {C U H J : Type*} [Fintype C] [Nonempty C] [Fintype U] [Fintype H] [Fintype J]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure ((C × U) × H)) [IsProbabilityMeasure θ] (h₀ : H)

/-- Expected lists are needed only on favorable data. The original bad-data
probability incurs a logarithmic penalty; exact (X,O) posterior independence
is used only in the subsequent one-package reduction. -/
theorem originalResamplingLaw_favorable_gap_information_lower_bound (j : J)
    (reject : C → H → Prop) (bad : Finset (C × U)) (M G D : ℝ) (hG : Real.log (1 + M) ≤ G)
    (hC : Real.log (Fintype.card C) ≤ G + D)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      ω.1.1 ∈ passingList reject ω.2) :
    condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      G - θ.real (Prod.fst ⁻¹' (bad : Set (C × U))) * D ≤
      condMutualInfo (fun ω : (C × U) × (J → H) => ω.1.1) Prod.snd
        (fun ω => ω.1.2) (originalResamplingLaw θ h₀) := by
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  have hl := condEntropy_le_integral_log_list (originalResamplingLaw (J := J) θ h₀)
    (fun ω => ω.1.1) (fun ω => (ω.2, ω.1.2)) (fun y => passingList reject y.1)
    (measurable_of_finite _) (measurable_of_finite _) hmem
  have hb := originalResamplingLaw_favorable_gap_log_budget θ h₀ reject bad M G D hG hC hbudget
  have he := IdentDistrib.condEntropy_eq (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
    (originalResamplingLaw_identDistrib θ h₀ (fun ω : (C × U) × H => (ω.1.1, ω.1.2)) j)
  rw [condMutualInfo_eq'
    (X := fun ω : (C × U) × (J → H) => ω.1.1)
    (Y := fun ω : (C × U) × (J → H) => ω.2)
    (Z := fun ω : (C × U) × (J → H) => ω.1.2)
    (measurable_of_finite (fun ω : (C × U) × (J → H) => ω.1.1))
    (measurable_of_finite (Prod.snd : (C × U) × (J → H) → J → H))
    (measurable_of_finite (fun ω : (C × U) × (J → H) => ω.1.2))
    (originalResamplingLaw θ h₀)]
  change condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ - _ - _ ≤ _ - _
  change _ ≤ ∫ ω, passingListLog reject ω.2 ∂originalResamplingLaw (J := J) θ h₀ at hl
  linarith

theorem originalResamplingLaw_favorable_gap_one_package_lower_bound (j : J)
    (reject : C → H → Prop) (bad : Finset (C × U)) (M G D : ℝ) (hG : Real.log (1 + M) ≤ G)
    (hC : Real.log (Fintype.card C) ≤ G + D)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      ω.1.1 ∈ passingList reject ω.2) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      G - θ.real (Prod.fst ⁻¹' (bad : Set (C × U))) * D) / Fintype.card J ≤
      condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ :=
  originalResamplingLaw_one_package_lower_from_budget θ h₀ j _
    (originalResamplingLaw_favorable_gap_information_lower_bound θ h₀ j reject bad M G D hG hC hbudget hmem)

end Information

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_gap_log_budget
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_gap_information_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_gap_one_package_lower_bound

#print axioms BinaryFormMoat.EntropyIntegration.root_passing_log_gap
