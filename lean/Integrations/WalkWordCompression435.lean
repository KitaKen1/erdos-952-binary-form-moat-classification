import Integrations.CheckpointCompression435
import Integrations.PosteriorRootLists435
import Integrations.WalkPassingLoss435

set_option quotPrecheck false

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- EVERY candidate's relative hit is a test of only physical displacement
and the finite increment word, not of hidden source times or residues. -/
theorem walk_wordPackageReject_relative_iff {Ω C : Type*} [AddCommGroup C]
    (z : ℕ → Point) (R S : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
    (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
    (φ : Point →+ C) (L : ℕ) (x : C) (ω : Ω) :
    wordPackageReject R S L φ x
      (walkDisplacement z R S hstep t u hforward hshift ω,
        wordAt (walkLetters z R hstep) L (u ω)) ↔
      ω ∈ wordHitSet (fun a => φ (z a)) u (fun ω => φ (z (t ω).val) - x) L := by
  simp only [wordPackageReject, wordHitSet, Set.mem_iUnion, wordHitEvent, Set.mem_ofPred_eq]
  apply exists_congr
  intro i
  have hp := walk_wordPrefixResidue z R hstep φ L (u ω) i
  change x + φ (z (u ω) - z (t ω).val) + _ = 0 ↔ _
  rw [map_sub]
  constructor <;> intro h
  · rw [hp]
    calc
      _ = (x + (φ (z (u ω)) - φ (z (t ω).val)) +
        wordPrefixResidue φ (wordAt (walkLetters z R hstep) L (u ω)) i) +
          φ (z (t ω).val) - x := by abel
      _ = _ := by rw [h, zero_add]
  · rw [hp] at h
    calc
      _ = (φ (z (u ω)) + wordPrefixResidue φ
        (wordAt (walkLetters z R hstep) L (u ω)) i) -
          (φ (z (t ω).val) - x) := by abel
      _ = 0 := by rw [h, sub_self]

section Walk
variable {Ω C U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype C] [AddCommGroup C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
  (φ : Point →+ C) (ψ : Point →+ U)

local notation "V" => (fun ω => (φ (z (t ω).val), ψ (z (t ω).val)))
/-- Conditioning on precisely (X,O) commutes with the actual package map. -/
theorem walkInformationCheckpointLaw_word_continuation_map (L : ℕ)
    (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (a : C × U) (ha : μ (V ⁻¹' {a}) ≠ 0) :
    originalContinuationLaw (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift
      φ ψ (fun ω => wordAt (walkLetters z R hstep) L (u ω))) h₀ a =
      (μ[|V ⁻¹' {a}]).map (fun ω => (walkDisplacement z R S hstep t u hforward hshift ω,
        wordAt (walkLetters z R hstep) L (u ω))) :=
  finiteCheckpointLaw_originalContinuation_map μ V _ h₀ a ha

/-- The rejection floor transfers to the ORIGINAL compressed posterior
law for every candidate, with no law or checkpoint substitution. -/
theorem walkInformationCheckpointLaw_relative_reject_real (L : ℕ)
    (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (a : C × U) (ha : μ (V ⁻¹' {a}) ≠ 0) (x : C) :
    (originalContinuationLaw (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift
      φ ψ (fun ω => wordAt (walkLetters z R hstep) L (u ω))) h₀ a).real
      {h | wordPackageReject R S L φ x h} =
      (μ[|V ⁻¹' {a}]).real
        (wordHitSet (fun a => φ (z a)) u (fun ω => φ (z (t ω).val) - x) L) := by
  rw [walkInformationCheckpointLaw, finiteCheckpointLaw_originalContinuation_real μ V _ h₀ a ha]
  congr 1
  ext ω
  exact walk_wordPackageReject_relative_iff z R S hstep t u hforward hshift φ L x ω

/-- Faithful (X,O) recording and zero avoidance imply almost-sure true-list
membership in the actual compressed posterior experiment. -/
theorem walkInformationCheckpointLaw_zero_avoiding_true_in_list {J : Type*} [Fintype J]
    (L : ℕ) (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (hzero : ∀ v, φ (z v) ≠ 0) :
    ∀ᵐ ω ∂originalResamplingLaw (J := J)
      (walkInformationCheckpointLaw μ z R S hstep t u hforward hshift
        φ ψ (fun ω => wordAt (walkLetters z R hstep) L (u ω))) h₀,
      ω.1.1 ∈ passingList (wordPackageReject R S L φ) ω.2 := by
  apply finiteCheckpointLaw_true_in_passingList μ V _ h₀ Prod.fst
  apply Filter.Eventually.of_forall
  intro ω h
  obtain ⟨i, hi⟩ := (walk_wordPackageReject_iff z R S hstep t u hforward hshift φ L ω).mp h
  exact hzero _ hi

end Walk

/-- Arithmetic zero avoidance supplies residue zero avoidance for a chosen
root. This uses actual homogenized values, not a root-level extra premise. -/
theorem rootResidueHom_ne_zero_of_not_dvd (f : Polynomial ℤ) (n : ℕ)
    (hn : f.natDegree ≤ n) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (z : Point)
    (havoid : ¬ p ∣ (value (f.homogenize n) z).natAbs) : rootResidueHom p ρ z ≠ 0 := by
  intro hz
  exact havoid (rootResidueHom_zero_dvd_value f n hn p ρ hρ z hz)

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.walk_wordPackageReject_relative_iff
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_word_continuation_map
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_relative_reject_real
#print axioms BinaryFormMoat.EntropyIntegration.walkInformationCheckpointLaw_zero_avoiding_true_in_list
#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_ne_zero_of_not_dvd
