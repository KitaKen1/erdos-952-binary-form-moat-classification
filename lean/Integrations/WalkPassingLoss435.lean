import Integrations.WalkPackageRate435
import Integrations.PassingLoss435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

def wordPrefixResidue {G : Type*} [AddCommGroup G] {R L : ℕ}
    (φ : Point →+ G) (w : Fin L → BoundedDisplacement R) (i : Fin L) : G :=
  ∑ k : Fin i.val, φ (w ⟨k.val, k.isLt.trans i.isLt⟩).val

/-- A candidate is rejected when its translated word meets residue zero. -/
def wordPackageReject {G : Type*} [AddCommGroup G] (R S L : ℕ) (φ : Point →+ G)
    (x : G) (h : BoundedDisplacement ((R + 1) * S) ×
      (Fin L → BoundedDisplacement (R + 1))) : Prop :=
  ∃ i : Fin L, x + φ h.1.val + wordPrefixResidue φ h.2 i = 0

theorem walk_wordPrefixResidue {G : Type*} [AddCommGroup G]
    (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : Point →+ G) (L u : ℕ) (i : Fin L) :
    φ (z (u + i)) = φ (z u) +
      wordPrefixResidue φ (wordAt (walkLetters z R hstep) L u) i := by
  have h := residue_shift_word_sum (walkLetters z R hstep) (fun v => φ v.val)
    (fun t => φ (z t)) (walkLetters_residue_step z R hstep φ) u i.val
  exact h

section Walk
variable {Ω C U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype C] [AddCommGroup C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
  (φ : Point →+ C) (ψ : Point →+ U)

local notation "d" => walkDisplacement z R S hstep t u hforward hshift

omit [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ] in
theorem walk_wordPackageReject_iff (L : ℕ) (ω : Ω) :
    wordPackageReject R S L φ (φ (z (t ω).val))
      (d ω, wordAt (walkLetters z R hstep) L (u ω)) ↔
      ∃ i : Fin L, φ (z (u ω + i)) = 0 := by
  unfold wordPackageReject
  apply exists_congr
  intro i
  have h := walk_wordPrefixResidue z R hstep φ L (u ω) i
  have hd : φ (z (t ω).val) + φ (d ω).val = φ (z (u ω)) := by
    change φ (z (t ω).val) + φ (z (u ω) - z (t ω).val) = _
    rw [map_sub]
    abel
  rw [hd, ← h]

omit [IsProbabilityMeasure μ] in
theorem walkInformationCheckpointLaw_word_reject_probability (L : ℕ) :
    (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
      (fun ω => wordAt (walkLetters z R hstep) L (u ω))).real
        {ω | wordPackageReject R S L φ ω.1.1 ω.2} =
      (μ.map u).real {v | ∃ i : Fin L, φ (z (v + i)) = 0} := by
  rw [walkInformationCheckpointLaw, finiteCheckpointLaw,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  exact walk_wordPackageReject_iff z R S hstep t u hforward hshift φ L ω

theorem walk_passingList_terminal_lower_bound_one_trial_error {K J : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype J]
    (W : Ω → K) (j : J) (w₀ : K)
    (reject : C → BoundedDisplacement ((R + 1) * S) × K → Prop)
    (E : C × U → Finset C) (ε : C × U → ℝ) (A : ℝ)
    (hfloor : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W)
      (Prod.fst ⁻¹' {a}) ≠ 0 → ∀ x ∉ E a,
      ε a ≤ (originalContinuationLaw
        (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W)
        (zeroDisplacement ((R + 1) * S), w₀) a).real {h | reject x h})
    (hE : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W)
      (Prod.fst ⁻¹' {a}) ≠ 0 → ((E a).card : ℝ) ≤ 4 * A)
    (ht : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W)
      (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ A) :
    (condEntropy (fun ω => φ (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ -
      Real.log 2 - Real.log (1 + 5 * A)) / Fintype.card J -
      μ.real {ω | reject (φ (z (t ω).val)) (d ω, W ω)} * Real.log (Fintype.card C) -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
    condMutualInfo (fun ω => φ (z (u ω))) W (fun ω => ψ (z (u ω))) μ := by
  have hl := originalResamplingLaw_passingList_lower_bound_one_trial_error
    (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W)
    (zeroDisplacement ((R + 1) * S), w₀) j reject E ε A hfloor hE ht
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information] at hl
  have he : (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ W).real
      {ω | reject ω.1.1 ω.2} =
      μ.real {ω | reject (φ (z (t ω).val)) (d ω, W ω)} := by
    rw [walkInformationCheckpointLaw, finiteCheckpointLaw,
      map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
    rfl
  rw [he] at hl
  have hu := walk_information_transport μ z R S hstep t u hforward hshift φ ψ W
  linarith

theorem walk_passingList_word_lower_bound_actual_error {J : Type*} [Fintype J]
    (L : ℕ) (j : J) (w₀ : Fin L → BoundedDisplacement (R + 1))
    (E : C × U → Finset C) (ε : C × U → ℝ) (A : ℝ)
    (hfloor : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
      (fun ω => wordAt (walkLetters z R hstep) L (u ω))) (Prod.fst ⁻¹' {a}) ≠ 0 →
      ∀ x ∉ E a, ε a ≤ (originalContinuationLaw
        (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
          (fun ω => wordAt (walkLetters z R hstep) L (u ω)))
        (zeroDisplacement ((R + 1) * S), w₀) a).real {h | wordPackageReject R S L φ x h})
    (hE : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
      (fun ω => wordAt (walkLetters z R hstep) L (u ω))) (Prod.fst ⁻¹' {a}) ≠ 0 →
      ((E a).card : ℝ) ≤ 4 * A)
    (ht : ∀ a, (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
      (fun ω => wordAt (walkLetters z R hstep) L (u ω))) (Prod.fst ⁻¹' {a}) ≠ 0 →
      Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε a) ≤ A) :
    (condEntropy (fun ω => φ (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ -
      Real.log 2 - Real.log (1 + 5 * A)) / Fintype.card J -
      (μ.map u).real {v | ∃ i : Fin L, φ (z (v + i)) = 0} * Real.log (Fintype.card C) -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
    condMutualInfo (fun v => φ (z v)) (wordAt (walkLetters z R hstep) L)
      (fun v => ψ (z v)) (μ.map u) := by
  have hl := originalResamplingLaw_passingList_lower_bound_one_trial_error
    (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift φ ψ
      (fun ω => wordAt (walkLetters z R hstep) L (u ω)))
    (zeroDisplacement ((R + 1) * S), w₀) j (wordPackageReject R S L φ) E ε A hfloor hE ht
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information,
    walkInformationCheckpointLaw_word_reject_probability] at hl
  have hu := walk_information_transport μ z R S hstep t u hforward hshift φ ψ
    (fun ω => wordAt (walkLetters z R hstep) L (u ω))
  rw [walk_terminal_word_information_map] at hu
  linarith

end Walk
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.walk_wordPrefixResidue
#print axioms BinaryFormMoat.EntropyIntegration.walk_wordPackageReject_iff
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_word_reject_probability
#print axioms BinaryFormMoat.EntropyIntegration.walk_passingList_terminal_lower_bound_one_trial_error
#print axioms BinaryFormMoat.EntropyIntegration.walk_passingList_word_lower_bound_actual_error
