import Integrations.PosteriorPassing435
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Lists
variable {Ω S T : Type*} [MeasurableSpace Ω] [Fintype S] [Fintype T]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem integral_list_card_eq_sum (Y : Ω → T) (L : T → Finset S) (hY : Measurable Y) :
    (∫ ω, ((L (Y ω)).card : ℝ) ∂μ) =
      ∑ y, μ.real (Y ⁻¹' {y}) * ((L y).card : ℝ) := by
  calc
    _ = ∫ y, ((L y).card : ℝ) ∂μ.map Y :=
      (integral_map hY.aemeasurable (measurable_of_finite _).aestronglyMeasurable).symm
    _ = _ := by
      rw [integral_fintype Integrable.of_finite]
      simp only [map_measureReal_apply hY (MeasurableSet.singleton _), smul_eq_mul]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Clamping empty lists costs at most one in the expected size, giving a
uniform Jensen bound without a nonempty-list assumption. -/
theorem mean_log_clamped_list_le (Y : Ω → T) (L : T → Finset S) (hY : Measurable Y)
    (M : ℝ) (hbudget : (∫ ω, ((L (Y ω)).card : ℝ) ∂μ) ≤ M) :
    (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) ≤
      Real.log (1 + M) := by
  have hw : ∑ y, μ.real (Y ⁻¹' {y}) = 1 :=
    fiber_weights_sum_one μ Y hY
  have hpos (y : T) : (0 : ℝ) < (max 1 (L y).card : ℕ) := by
    exact_mod_cast (show 0 < max 1 (L y).card by omega)
  have hj := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).le_map_sum
    (t := Finset.univ) (w := fun y => μ.real (Y ⁻¹' {y}))
    (p := fun y => ((max 1 (L y).card : ℕ) : ℝ))
    (fun _ _ => measureReal_nonneg) hw (fun y _ => hpos y)
  simp only [smul_eq_mul] at hj
  have hlower : 1 ≤ ∑ y, μ.real (Y ⁻¹' {y}) * ((max 1 (L y).card : ℕ) : ℝ) := by
    calc
      _ = ∑ y, μ.real (Y ⁻¹' {y}) * 1 := by simpa only [mul_one] using hw.symm
      _ ≤ _ := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.le_max_left 1 (L y).card) measureReal_nonneg)
  have hupper : (∑ y, μ.real (Y ⁻¹' {y}) * ((max 1 (L y).card : ℕ) : ℝ)) ≤ 1 + M := by
    calc
      _ ≤ ∑ y, μ.real (Y ⁻¹' {y}) * (1 + ((L y).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        exact_mod_cast (show max 1 (L y).card ≤ 1 + (L y).card by omega)
      _ = 1 + ∫ ω, ((L (Y ω)).card : ℝ) ∂μ := by
        simp_rw [mul_add, mul_one]
        rw [Finset.sum_add_distrib, hw, ← integral_list_card_eq_sum μ Y L hY]
      _ ≤ _ := add_le_add (le_refl 1) hbudget
  exact hj.trans (Real.log_le_log (by linarith) hupper)

theorem condEntropy_le_expected_list_card (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℝ)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ L (Y ω))
    (hbudget : (∫ ω, ((L (Y ω)).card : ℝ) ∂μ) ≤ M) :
    condEntropy X Y μ ≤ Real.log (1 + M) :=
  (condEntropy_le_log_list_of_ae_mem μ X Y L hX hY hmem).trans
    (mean_log_clamped_list_le μ Y L hY M hbudget)

theorem mutualInfo_ge_expected_list_card (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℝ)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ L (Y ω))
    (hbudget : (∫ ω, ((L (Y ω)).card : ℝ) ∂μ) ≤ M) :
    entropy X μ - Real.log (1 + M) ≤ mutualInfo X Y μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  have h := condEntropy_le_expected_list_card μ X Y L hX hY M hmem hbudget
  linarith

theorem condMutualInfo_ge_expected_list_card {U : Type*} [Fintype U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (L : T × U → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (M : ℝ)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ L (Y ω, Z ω))
    (hbudget : (∫ ω, ((L (Y ω, Z ω)).card : ℝ) ∂μ) ≤ M) :
    condEntropy X Z μ - Real.log (1 + M) ≤ condMutualInfo X Y Z μ := by
  rw [condMutualInfo_eq' hX hY hZ]
  have h := condEntropy_le_expected_list_card μ X (fun ω => (Y ω, Z ω)) L hX
    (hY.prodMk hZ) M hmem hbudget
  linarith

theorem condEntropy_le_expected_list_card_error (X : Ω → S) (Y : Ω → T)
    (L : T → Finset S) (hX : Measurable X) (hY : Measurable Y) (M : ℝ)
    (hbudget : (∫ ω, ((L (Y ω)).card : ℝ) ∂μ) ≤ M) :
    condEntropy X Y μ ≤ Real.log 2 + Real.log (1 + M) +
      μ.real {ω | X ω ∉ L (Y ω)} * Real.log (Fintype.card S) := by
  let : MeasurableSpace Bool := ⊤
  have h := condEntropy_le_error_aware_list μ X Y L hX hY
  have hj := mean_log_clamped_list_le μ Y L hY M hbudget
  linarith

theorem condMutualInfo_ge_expected_list_card_error {U : Type*} [Fintype U]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (L : T × U → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (M : ℝ)
    (hbudget : (∫ ω, ((L (Y ω, Z ω)).card : ℝ) ∂μ) ≤ M) :
    condEntropy X Z μ - Real.log 2 - Real.log (1 + M) -
      μ.real {ω | X ω ∉ L (Y ω, Z ω)} * Real.log (Fintype.card S) ≤
      condMutualInfo X Y Z μ := by
  rw [condMutualInfo_eq' hX hY hZ]
  have h := condEntropy_le_expected_list_card_error μ X (fun ω => (Y ω, Z ω)) L hX
    (hY.prodMk hZ) M hbudget
  linarith

end Lists

/-- The prior entropy is that of the original joint law, while the list
and information use its constructed posterior packages. True-value survival
is an explicit premise; no independence of the prior variables is inferred. -/
theorem originalResamplingLaw_passingList_information_lower_bound
    {A H J C U : Type*} [Fintype A] [Fintype H] [Fintype J] [Fintype C] [Fintype U]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H) (j : J)
    (X : A → C) (O : A → U) (reject : C → H → Prop)
    (B : A → Finset C) (ε : A → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀, X ω.1 ∈ passingList reject ω.2) :
    condEntropy (fun ω : A × H => X ω.1) (fun ω => O ω.1) θ - Real.log (1 + 5 * M) ≤
      condMutualInfo (fun ω : A × (J → H) => X ω.1) Prod.snd (fun ω => O ω.1)
        (originalResamplingLaw θ h₀) := by
  classical
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  have hid := originalResamplingLaw_identDistrib θ h₀ (fun ω : A × H => (X ω.1, O ω.1)) j
  have he : condEntropy (fun ω : A × (J → H) => X ω.1) (fun ω => O ω.1)
      (originalResamplingLaw θ h₀) =
      condEntropy (fun ω : A × H => X ω.1) (fun ω => O ω.1) θ :=
    IdentDistrib.condEntropy_eq (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) hid
  have hbudget := originalResamplingLaw_expected_passingList_source_bound (J := J)
    θ h₀ reject B ε M hfloor hB ht
  have h := condMutualInfo_ge_expected_list_card (originalResamplingLaw (J := J) θ h₀)
    (fun ω => X ω.1) Prod.snd (fun ω => O ω.1) (fun y => passingList reject y.1)
    (measurable_of_finite _) measurable_snd (measurable_of_finite _) (5 * M) hmem hbudget
  rw [he] at h
  exact h

/-- The version needed when a finite distinct-prime budget permits true
values to be rejected: their actual loss probability is explicitly charged. -/
theorem originalResamplingLaw_passingList_information_lower_bound_error
    {A H J C U : Type*} [Fintype A] [Fintype H] [Fintype J] [Fintype C] [Fintype U]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H) (j : J)
    (X : A → C) (O : A → U) (reject : C → H → Prop)
    (B : A → Finset C) (ε : A → ℝ) (M : ℝ)
    (hfloor : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ B a,
      ε a ≤ (originalContinuationLaw θ h₀ a).real {h | reject x h})
    (hB : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ 4 * M)
    (ht : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ M) :
    condEntropy (fun ω : A × H => X ω.1) (fun ω => O ω.1) θ - Real.log 2 -
      Real.log (1 + 5 * M) - (originalResamplingLaw (J := J) θ h₀).real
        {ω | X ω.1 ∉ passingList reject ω.2} * Real.log (Fintype.card C) ≤
      condMutualInfo (fun ω : A × (J → H) => X ω.1) Prod.snd (fun ω => O ω.1)
        (originalResamplingLaw θ h₀) := by
  classical
  have : IsProbabilityMeasure (originalResamplingLaw (J := J) θ h₀) := by
    unfold originalResamplingLaw
    infer_instance
  have hid := originalResamplingLaw_identDistrib θ h₀ (fun ω : A × H => (X ω.1, O ω.1)) j
  have he : condEntropy (fun ω : A × (J → H) => X ω.1) (fun ω => O ω.1)
      (originalResamplingLaw θ h₀) =
      condEntropy (fun ω : A × H => X ω.1) (fun ω => O ω.1) θ :=
    IdentDistrib.condEntropy_eq (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) hid
  have hbudget := originalResamplingLaw_expected_passingList_source_bound (J := J)
    θ h₀ reject B ε M hfloor hB ht
  have h := condMutualInfo_ge_expected_list_card_error (originalResamplingLaw (J := J) θ h₀)
    (fun ω => X ω.1) Prod.snd (fun ω => O ω.1) (fun y => passingList reject y.1)
    (measurable_of_finite _) measurable_snd (measurable_of_finite _) (5 * M) hbudget
  rw [he] at h
  exact h

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.integral_list_card_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.mean_log_clamped_list_le
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_expected_list_card
#print axioms BinaryFormMoat.EntropyIntegration.mutualInfo_ge_expected_list_card
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_ge_expected_list_card
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_expected_list_card_error
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_ge_expected_list_card_error
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_information_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_passingList_information_lower_bound_error
