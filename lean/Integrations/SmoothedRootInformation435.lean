import Integrations.SmoothedRootPackage435
import Integrations.PosteriorLogLists435

set_option quotPrecheck false

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

section Smoothed
variable {Ω A U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
  (N : ℕ) [NeZero N] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ))
  {M : ℕ} (t : A → Fin M)
  (hforward : ∀ ω : Ω × Fin N, (t (σ ω.1)).val ≤ b ω.1 + ω.2.val)
  (hshift : ∀ ω : Ω × Fin N, b ω.1 + ω.2.val ≤ (t (σ ω.1)).val + S)
  (p : ℕ) [NeZero p] (ρ : ZMod p) (ψ : Point →+ U) (L : ℕ)

local notation "μ" => ν.prod (uniformOn (Set.univ : Set (Fin N)))
local notation "q" => (fun ω : Ω × Fin N => t (σ ω.1))
local notation "u" => (fun ω : Ω × Fin N => b ω.1 + ω.2.val)
local notation "φ" => rootResidueHom p ρ
local notation "F" => (fun a : A => (φ (z (t a).val), ψ (z (t a).val)))
local notation "Θ" => walkInformationCheckpointLaw μ z R S hstep q u hforward hshift φ ψ
  (fun ω => wordAt (walkLetters z R hstep) L (u ω))

/-- ACTUAL terminal-word information from favorable compressed lists,
original bad-data mass and arithmetic true-list support. Both displacement
entropy costs are paid. This is a conditional lower bound, not yet a positive
all-batch c/log(T) rate: lengths, thresholds and averaging remain to supply. -/
theorem smoothedRootPackage_information_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (bad : Finset (ZMod p × U))
    (hbad : ∀ a ∉ bad, Θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      fiberConditionalReal μ (fun ω => F (σ ω.1)) a
      {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)} ≤
        (1 : ℝ) / 2)
    (havoid : ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    (condEntropy (fun ω => φ (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      Real.log (1 + 5 * (p : ℝ) ^ (1 - β)) -
      (μ).real ((fun ω => F (σ ω.1)) ⁻¹' (bad : Set (ZMod p × U))) * Real.log p) /
        paperPassingCount T L τ β - 4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      condMutualInfo (fun v => φ (z v)) (wordAt (walkLetters z R hstep) L)
        (fun v => ψ (z v)) ((μ).map u) := by
  let m := paperPassingCount T L τ β
  let j : Fin m := ⟨0, paperPassingCount_pos T L τ β⟩
  let h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)) :=
    (zeroDisplacement ((R + 1) * S), fun _ => zeroDisplacement (R + 1))
  have hmem := smoothedRootPackage_avoiding_true_in_list (J := Fin m) ν σ b N z R S hstep t
    hforward hshift p ρ ψ L h₀ f hρ havoid
  have hb (a : ZMod p × U) (hab : a ∉ bad) (ha : Θ (Prod.fst ⁻¹' {a}) ≠ 0) :
      (∫ h : Fin m → BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)),
        ((passingList (wordPackageReject R S L φ) h).card : ℝ)
        ∂Measure.pi (fun _ : Fin m => originalContinuationLaw Θ h₀ a)) ≤
          5 * (p : ℝ) ^ (1 - β) := by
    exact smoothedRootPackage_favorable_expected_list ν σ b N z R S hstep t
      hforward hshift p ρ ψ L h₀ a ha f hf hdeg hρ hz T hT hL hlo hhi
      hsmall τ β hτ hβ herr (hbad a hab ha)
  have hi := originalResamplingLaw_favorable_one_package_lower_bound Θ h₀ j
    (wordPackageReject R S L φ) bad (5 * (p : ℝ) ^ (1 - β)) (by positivity) hb hmem
  have he : (Θ).real (Prod.fst ⁻¹' (bad : Set (ZMod p × U))) =
      (μ).real ((fun ω => F (σ ω.1)) ⁻¹' (bad : Set (ZMod p × U))) := by
    rw [walkInformationCheckpointLaw, finiteCheckpointLaw,
      map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
    rfl
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information, he, Fintype.card_fin, ZMod.card] at hi
  have ht := walk_information_transport μ z R S hstep q u hforward hshift φ ψ
    (fun ω => wordAt (walkLetters z R hstep) L (u ω))
  rw [walk_terminal_word_information_map] at ht
  change (_ - _ - _) / (paperPassingCount T L τ β : ℝ) ≤ _ at hi
  linarith

end Smoothed
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_information_lower_bound
