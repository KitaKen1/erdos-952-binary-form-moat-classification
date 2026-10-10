import Integrations.PosteriorPackageInformation435
import Integrations.WalkLaw435
import Integrations.WalkWordBudget435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Walk
variable {Ω C U K : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype C] [AddCommGroup C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
  (φ : Point →+ C) (ψ : Point →+ U) (W : Ω → K)

/-- Coarsen the original finite source to exactly (X,O) before posterior
sampling. Its one-package law remains the actual displacement/word law. -/
noncomputable def walkInformationCheckpointLaw :
    Measure ((C × U) × (BoundedDisplacement ((R + 1) * S) × K)) :=
  finiteCheckpointLaw μ (fun ω => (φ (z (t ω).val), ψ (z (t ω).val)))
    (fun ω => (walkDisplacement z R S hstep t u hforward hshift ω, W ω))

instance walkInformationCheckpointLaw_isProbabilityMeasure :
    IsProbabilityMeasure (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W) := by
  unfold walkInformationCheckpointLaw
  infer_instance

local notation "Θ" => walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W
local notation "d" => walkDisplacement z R S hstep t u hforward hshift

theorem walkInformationCheckpointLaw_one_package_information :
    condMutualInfo (fun ω => ω.1.1) Prod.snd (fun ω => ω.1.2) Θ =
    condMutualInfo (fun ω => φ (z (t ω).val)) (fun ω => (d ω, W ω))
      (fun ω => ψ (z (t ω).val)) μ := by
  exact condMutualInfo_eq_of_identDistrib Θ μ _ _ _ _ _ _
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (finiteCheckpointLaw_identDistrib μ
      (fun ω => (φ (z (t ω).val), ψ (z (t ω).val))) (fun ω => (d ω, W ω))
      (fun ah => (ah.1.1, (ah.2, ah.1.2))))

theorem walkInformationCheckpointLaw_prior_condEntropy :
    condEntropy (fun ω => ω.1.1) (fun ω => ω.1.2) Θ =
    condEntropy (fun ω => φ (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ := by
  exact IdentDistrib.condEntropy_eq (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
    (finiteCheckpointLaw_identDistrib μ
      (fun ω => (φ (z (t ω).val), ψ (z (t ω).val))) (fun ω => (d ω, W ω))
      (fun ah => (ah.1.1, ah.1.2)))

include hstep hforward hshift in
/-- The actual walk displacement has a finite box alphabet, so two
entropy costs are bounded by four logarithms of its side length. -/
theorem walk_information_transport :
    condMutualInfo (fun ω => φ (z (t ω).val)) (fun ω => (d ω, W ω))
      (fun ω => ψ (z (t ω).val)) μ ≤
    condMutualInfo (fun ω => φ (z (u ω))) W (fun ω => ψ (z (u ω))) μ +
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) := by
  have h := condMutualInfo_additive_transport μ (fun ω => φ (z (t ω).val)) W
    (fun ω => ψ (z (t ω).val)) d (fun v => φ v.val) (fun v => ψ v.val)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)
  have hx : (fun ω => φ (z (t ω).val) + φ (d ω).val) = (fun ω => φ (z (u ω))) := by
    funext ω
    change φ (z (t ω).val) + φ (z (u ω) - z (t ω).val) = _
    rw [map_sub]
    abel
  have ho : (fun ω => ψ (z (t ω).val) + ψ (d ω).val) = (fun ω => ψ (z (u ω))) := by
    funext ω
    change ψ (z (t ω).val) + ψ (z (u ω) - z (t ω).val) = _
    rw [map_sub]
    abel
  rw [hx, ho] at h
  have hd : entropy d μ ≤ 2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) := by
    have hb := entropy_le_log_card d μ
    simpa only [boundedDisplacement_card, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hb
  linarith

include hstep hforward hshift in
theorem walk_information_transport_source_bound (B : ℝ)
    (hS : Real.log (S + 1 : ℕ) ≤ B) :
    condMutualInfo (fun ω => φ (z (t ω).val)) (fun ω => (d ω, W ω))
      (fun ω => ψ (z (t ω).val)) μ ≤
    condMutualInfo (fun ω => φ (z (u ω))) W (fun ω => ψ (z (u ω))) μ +
      4 * B + 4 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  have ht := walk_information_transport μ z R S hstep t u hforward hshift φ ψ W
  have hb := displacement_log_bound (R + 1) S
  linarith

theorem walk_resampled_package_information_le_terminal {J : Type*} [Fintype J] (w₀ : K) :
    condMutualInfo (fun ω => ω.1.1) Prod.snd (fun ω => ω.1.2)
      (originalResamplingLaw (J := J) Θ (zeroDisplacement ((R + 1) * S), w₀)) ≤
    (Fintype.card J : ℝ) * (condMutualInfo (fun ω => φ (z (u ω))) W
      (fun ω => ψ (z (u ω))) μ + 4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ)) := by
  have hp := originalResamplingLaw_package_condMutualInfo_le (J := J) Θ
    (zeroDisplacement ((R + 1) * S), w₀)
  rw [walkInformationCheckpointLaw_one_package_information] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (walk_information_transport μ z R S hstep t u hforward hshift φ ψ W)
    (Nat.cast_nonneg _))

theorem walk_passingList_terminal_information_lower_bound {J : Type*} [Fintype J]
    (j : J) (w₀ : K) (reject : C → BoundedDisplacement ((R + 1) * S) × K → Prop)
    (E : C × U → Finset C) (ε : C × U → ℝ) (A : ℝ)
    (hfloor : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ E a,
      ε a ≤ (originalContinuationLaw Θ (zeroDisplacement ((R + 1) * S), w₀) a).real
        {h | reject x h})
    (hE : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((E a).card : ℝ) ≤ 4 * A)
    (ht : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ A)
    (hmem : ∀ᵐ ω ∂originalResamplingLaw (J := J) Θ (zeroDisplacement ((R + 1) * S), w₀),
      ω.1.1 ∈ passingList reject ω.2) :
    (condEntropy (fun ω => φ (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ -
      Real.log (1 + 5 * A)) / Fintype.card J -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
    condMutualInfo (fun ω => φ (z (u ω))) W (fun ω => ψ (z (u ω))) μ := by
  have hl := originalResamplingLaw_passingList_one_package_lower_bound Θ
    (zeroDisplacement ((R + 1) * S), w₀) j reject E ε A hfloor hE ht hmem
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information] at hl
  have hu := walk_information_transport μ z R S hstep t u hforward hshift φ ψ W
  linarith

theorem walk_passingList_terminal_information_lower_bound_error {J : Type*} [Fintype J]
    (j : J) (w₀ : K) (reject : C → BoundedDisplacement ((R + 1) * S) × K → Prop)
    (E : C × U → Finset C) (ε : C × U → ℝ) (A : ℝ)
    (hfloor : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ E a,
      ε a ≤ (originalContinuationLaw Θ (zeroDisplacement ((R + 1) * S), w₀) a).real
        {h | reject x h})
    (hE : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 → ((E a).card : ℝ) ≤ 4 * A)
    (ht : ∀ a, Θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ A) :
    (condEntropy (fun ω => φ (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ - Real.log 2 -
      Real.log (1 + 5 * A) -
      (originalResamplingLaw (J := J) Θ (zeroDisplacement ((R + 1) * S), w₀)).real
        {ω | ω.1.1 ∉ passingList reject ω.2} * Real.log (Fintype.card C)) / Fintype.card J -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
    condMutualInfo (fun ω => φ (z (u ω))) W (fun ω => ψ (z (u ω))) μ := by
  have hl := originalResamplingLaw_passingList_one_package_lower_bound_error Θ
    (zeroDisplacement ((R + 1) * S), w₀) j reject E ε A hfloor hE ht
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information] at hl
  have hu := walk_information_transport μ z R S hstep t u hforward hshift φ ψ W
  linarith

/-- A terminal word and its residues use exactly the pushforward of the
original terminal time, the law required by the common-word upper budget. -/
theorem walk_terminal_word_information_map (L : ℕ) :
    condMutualInfo (fun ω => φ (z (u ω)))
      (fun ω => wordAt (walkLetters z R hstep) L (u ω)) (fun ω => ψ (z (u ω))) μ =
    condMutualInfo (fun v => φ (z v)) (wordAt (walkLetters z R hstep) L)
      (fun v => ψ (z v)) (μ.map u) := by
  have : IsProbabilityMeasure (μ.map u) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_finite u).aemeasurable).mpr inferInstance
  apply condMutualInfo_eq_of_identDistrib μ (μ.map u) _ _ _ _ _ _
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _)
  exact ⟨(measurable_of_finite _).aemeasurable, (measurable_of_countable _).aemeasurable,
    (Measure.map_map (μ := μ) (measurable_of_countable
      (fun v => (φ (z v), (wordAt (walkLetters z R hstep) L v, ψ (z v)))))
      (measurable_of_finite u)).symm⟩

theorem walk_resampled_word_information_le_terminal {J : Type*} [Fintype J]
    (L : ℕ) (w₀ : Fin L → BoundedDisplacement (R + 1)) :
    condMutualInfo (fun ω => ω.1.1) Prod.snd (fun ω => ω.1.2)
      (originalResamplingLaw (J := J)
        (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
          (fun ω => wordAt (walkLetters z R hstep) L (u ω)))
        (zeroDisplacement ((R + 1) * S), w₀)) ≤
    (Fintype.card J : ℝ) * (condMutualInfo (fun v => φ (z v))
      (wordAt (walkLetters z R hstep) L) (fun v => ψ (z v)) (μ.map u) +
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ)) := by
  have h := walk_resampled_package_information_le_terminal (J := J) μ z R S hstep t u
    hforward hshift φ ψ (fun ω => wordAt (walkLetters z R hstep) L (u ω)) w₀
  rwa [walk_terminal_word_information_map] at h

end Walk
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_one_package_information
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_prior_condEntropy
#print axioms BinaryFormMoat.EntropyIntegration.walk_information_transport
#print axioms BinaryFormMoat.EntropyIntegration.walk_information_transport_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.walk_resampled_package_information_le_terminal
#print axioms BinaryFormMoat.EntropyIntegration.walk_passingList_terminal_information_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.walk_passingList_terminal_information_lower_bound_error
#print axioms BinaryFormMoat.EntropyIntegration.walk_terminal_word_information_map
#print axioms BinaryFormMoat.EntropyIntegration.walk_resampled_word_information_le_terminal
