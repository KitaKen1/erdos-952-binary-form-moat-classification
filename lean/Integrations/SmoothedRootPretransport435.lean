import Integrations.SmoothedRootPackage435
import Integrations.PosteriorGapLog435
import Integrations.PosteriorBadData435
import Integrations.PaperPosteriorFavorable435

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

include hforward hshift

/-- Keep the ACTUAL one-package information before displacement transport.
The same common integer quota multiplies each coordinate information; actual
prefix chain rules may therefore combine them before paying displacement ONCE.
Canonical bad mass remains explicit for the actual coordinate-wise average. -/
theorem smoothedRootPackage_gap_pretransport_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (hβ₁ : β ≤ 1)
    (havoid : ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    let E : Set (Ω × Fin N) := {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
      (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)}
    let V := fun ω : Ω × Fin N => F (σ ω.1)
    condEntropy (fun ω => φ (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      ((1 - β) * Real.log p + Real.log 6) -
      (μ).real (V ⁻¹' (posteriorBadData μ V E : Set (ZMod p × U))) * (β * Real.log p) ≤
      (paperPassingCount T L τ β : ℝ) *
      condMutualInfo (fun ω => φ (z (q ω).val))
        (fun ω => (walkDisplacement z R S hstep q u hforward hshift ω,
          wordAt (walkLetters z R hstep) L (u ω)))
        (fun ω => ψ (z (q ω).val)) μ := by
  let V := fun ω : Ω × Fin N => F (σ ω.1)
  let E : Set (Ω × Fin N) := {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
    (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)}
  let bad := posteriorBadData μ V E
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
      hsmall τ β hτ hβ herr (posteriorBadData_favorable μ V E a hab)
  have hg := root_passing_log_gap p (by omega) β hβ₁
  have hi := originalResamplingLaw_favorable_gap_one_package_lower_bound Θ h₀ j
    (wordPackageReject R S L φ) bad (5 * (p : ℝ) ^ (1 - β))
    ((1 - β) * Real.log p + Real.log 6) (β * Real.log p) hg.1
    (by simpa only [ZMod.card] using hg.2) hb hmem
  have he : (Θ).real (Prod.fst ⁻¹' (bad : Set (ZMod p × U))) =
      (μ).real ((fun ω => F (σ ω.1)) ⁻¹' (bad : Set (ZMod p × U))) := by
    rw [walkInformationCheckpointLaw, finiteCheckpointLaw,
      map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
    rfl
  rw [walkInformationCheckpointLaw_prior_condEntropy,
    walkInformationCheckpointLaw_one_package_information, he, Fintype.card_fin] at hi
  change (_ - _ - _) / (paperPassingCount T L τ β : ℝ) ≤ _ at hi
  have hm : (0 : ℝ) < paperPassingCount T L τ β := by
    exact_mod_cast paperPassingCount_pos T L τ β
  have h := (div_le_iff₀ hm).mp hi
  simpa only [mul_comm] using h

end Smoothed
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_gap_pretransport_lower_bound
