import Integrations.CheckpointCompression435
import Integrations.ExpectedListEntropy435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

def passingListLog {C H J : Type*} [Fintype C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) : ℝ :=
  Real.log ((max 1 (passingList reject h).card : ℕ) : ℝ)

theorem passingListLog_le_log_card {C H J : Type*} [Fintype C] [Nonempty C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) :
    passingListLog reject h ≤ Real.log (Fintype.card C) := by
  unfold passingListLog
  apply Real.log_le_log (by positivity)
  exact_mod_cast (max_le (Fintype.card_pos_iff.mpr inferInstance)
    (Finset.card_le_univ (passingList reject h)))

/-- Jensen is applied separately inside each original posterior, so bad
data values will pay log(card C), not a global expected-cardinality loss. -/
theorem integral_passingListLog_le {C H J : Type*} [Fintype C] [Fintype H] [Fintype J]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (ν : Measure H) [IsProbabilityMeasure ν] (reject : C → H → Prop) (M : ℝ)
    (hbudget : (∫ h : J → H, ((passingList reject h).card : ℝ)
      ∂Measure.pi (fun _ : J => ν)) ≤ M) :
    (∫ h : J → H, passingListLog reject h ∂Measure.pi (fun _ : J => ν)) ≤
      Real.log (1 + M) := by
  have hj := mean_log_clamped_list_le (Measure.pi (fun _ : J => ν)) id
    (passingList reject) measurable_id M hbudget
  simpa only [integral_fintype Integrable.of_finite, passingListLog,
    smul_eq_mul, Set.preimage_id] using hj

theorem originalResamplingLaw_integral_package {A H J : Type*}
    [Fintype A] [Fintype H] [Fintype J]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H) (g : (J → H) → ℝ) :
    (∫ ω, g ω.2 ∂originalResamplingLaw (J := J) θ h₀) =
      ∑ a, (θ.map Prod.fst).real {a} *
        (∫ h : J → H, g h ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) := by
  rw [originalResamplingLaw, continuationResamplingLaw,
    integral_finsetSum_measure (fun _ _ =>
      Integrable.of_finite.smul_measure (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_smul_measure, integral_map (measurable_of_finite (Prod.mk a)).aemeasurable
    (measurable_of_finite (fun ω : A × (J → H) => g ω.2)).aestronglyMeasurable]
  rfl

/-- Bad posterior data pay only their ORIGINAL probability times log(card C).
Zero original fibers cancel, even though their fillers are probability laws. -/
theorem originalResamplingLaw_favorable_log_budget {A H J C : Type*}
    [Fintype A] [Fintype H] [Fintype J] [Fintype C] [Nonempty C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)
    (reject : C → H → Prop) (bad : Finset A) (M : ℝ) (hM : 0 ≤ M)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M) :
    (∫ ω, passingListLog reject ω.2 ∂originalResamplingLaw (J := J) θ h₀) ≤
      Real.log (1 + M) + θ.real (Prod.fst ⁻¹' (bad : Set A)) * Real.log (Fintype.card C) := by
  let w := fun a : A => (θ.map Prod.fst).real {a}
  have hw : ∑ a, w a = 1 := by simp [w]
  have hl : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
  have hf (a : A) : w a *
      (∫ h : J → H, passingListLog reject h
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤
      w a * (Real.log (1 + M) + if a ∈ bad then Real.log (Fintype.card C) else 0) := by
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
        linarith
      · simp only [hb, ite_false, add_zero]
        exact integral_passingListLog_le _ reject M (hbudget a hb ha)
  rw [originalResamplingLaw_integral_package]
  calc
    _ ≤ ∑ a, w a * (Real.log (1 + M) + if a ∈ bad then Real.log (Fintype.card C) else 0) :=
      Finset.sum_le_sum (fun a _ => hf a)
    _ = Real.log (1 + M) + (∑ a ∈ bad, w a) * Real.log (Fintype.card C) := by
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

/-- The conditional list-support bound as an integral, retaining original
weights rather than imposing a uniform cardinality cutoff. -/
theorem condEntropy_le_integral_log_list {Ω C D : Type*} [MeasurableSpace Ω]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → C) (Y : Ω → D) (L : D → Finset C)
    (hX : Measurable X) (hY : Measurable Y) (hmem : ∀ᵐ ω ∂μ, X ω ∈ L (Y ω)) :
    condEntropy X Y μ ≤ ∫ ω, Real.log ((max 1 (L (Y ω)).card : ℕ) : ℝ) ∂μ := by
  have he : (∫ ω, Real.log ((max 1 (L (Y ω)).card : ℕ) : ℝ) ∂μ) =
      ∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ) := by
    calc
      _ = ∫ y, Real.log ((max 1 (L y).card : ℕ) : ℝ) ∂μ.map Y :=
        (integral_map hY.aemeasurable (measurable_of_finite _).aestronglyMeasurable).symm
      _ = _ := by
        rw [integral_fintype Integrable.of_finite]
        simp only [map_measureReal_apply hY (MeasurableSet.singleton _), smul_eq_mul]
  exact (condEntropy_le_log_list_of_ae_mem μ X Y L hX hY hmem).trans_eq he.symm

section Information
variable {C U H J : Type*} [Fintype C] [Nonempty C] [Fintype U] [Fintype H] [Fintype J]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure ((C × U) × H)) [IsProbabilityMeasure θ] (h₀ : H)

/-- Expected lists are needed only on favorable data. The original bad-data
probability incurs a logarithmic penalty; exact (X,O) posterior independence
is used only in the subsequent one-package reduction. -/
theorem originalResamplingLaw_favorable_information_lower_bound (j : J)
    (reject : C → H → Prop) (bad : Finset (C × U)) (M : ℝ) (hM : 0 ≤ M)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      ω.1.1 ∈ passingList reject ω.2) :
    condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      Real.log (1 + M) - θ.real (Prod.fst ⁻¹' (bad : Set (C × U))) *
        Real.log (Fintype.card C) ≤
      condMutualInfo (fun ω : (C × U) × (J → H) => ω.1.1) Prod.snd
        (fun ω => ω.1.2) (originalResamplingLaw θ h₀) := by
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  have hl := condEntropy_le_integral_log_list (originalResamplingLaw (J := J) θ h₀)
    (fun ω => ω.1.1) (fun ω => (ω.2, ω.1.2)) (fun y => passingList reject y.1)
    (measurable_of_finite _) (measurable_of_finite _) hmem
  have hb := originalResamplingLaw_favorable_log_budget θ h₀ reject bad M hM hbudget
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

theorem originalResamplingLaw_favorable_one_package_lower_bound (j : J)
    (reject : C → H → Prop) (bad : Finset (C × U)) (M : ℝ) (hM : 0 ≤ M)
    (hbudget : ∀ a ∉ bad, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      (∫ h : J → H, ((passingList reject h).card : ℝ)
        ∂Measure.pi (fun _ : J => originalContinuationLaw θ h₀ a)) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      ω.1.1 ∈ passingList reject ω.2) :
    (condEntropy (fun ω : (C × U) × H => ω.1.1) (fun ω => ω.1.2) θ -
      Real.log (1 + M) - θ.real (Prod.fst ⁻¹' (bad : Set (C × U))) *
        Real.log (Fintype.card C)) / Fintype.card J ≤
      condMutualInfo (fun ω : (C × U) × H => ω.1.1) Prod.snd (fun ω => ω.1.2) θ :=
  originalResamplingLaw_one_package_lower_from_budget θ h₀ j _
    (originalResamplingLaw_favorable_information_lower_bound θ h₀ j reject bad M hM hbudget hmem)

end Information
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.passingListLog
#print axioms BinaryFormMoat.EntropyIntegration.passingListLog_le_log_card
#print axioms BinaryFormMoat.EntropyIntegration.integral_passingListLog_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_integral_package
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_log_budget
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_integral_log_list
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_information_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_favorable_one_package_lower_bound
