import Integrations.SmoothedRootGapInformation435
import Integrations.PaperPosteriorFavorable435

set_option quotPrecheck false
noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory GeometryIntegration
attribute [local irreducible] paperPassingCount

section Smoothed
variable {Ω U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (r b : Ω → ℕ)
  (N : ℕ) [NeZero N] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ))
  (hforward : ∀ ω : Ω × Fin N, r ω.1 ≤ b ω.1 + ω.2.val)
  (hshift : ∀ ω : Ω × Fin N, b ω.1 + ω.2.val ≤ r ω.1 + S)
  (p : ℕ) [NeZero p] (ρ : ZMod p) (ψ : Point →+ U) (L : ℕ)

local notation "μ" => ν.prod (uniformOn (Set.univ : Set (Fin N)))
local notation "u" => (fun ω : Ω × Fin N => b ω.1 + ω.2.val)
local notation "φ" => rootResidueHom p ρ
include hforward hshift

/-- Natural checkpoint times are encoded losslessly on the ACTUAL source.
The source-smoothing failure event is EXACTLY the original natural-time
coverage event used by backward coverage, including zero original fibers.
No finite checkpoint bound, finer-history conditioning or new law is assumed. -/
theorem smoothedRootPackage_exact_checkpoint_gap_information_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2) (hβ₁ : β ≤ 1)
    (havoid : ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    (condEntropy (fun ω => φ (z (r ω.1))) (fun ω => ψ (z (r ω.1))) μ -
      ((1 - β) * Real.log p + Real.log 6) -
      2 * (μ).real (exactCheckpointBadEvent μ (fun ω => r ω.1) (fun _ : Unit => ZMod p)
        (fun _ ω => φ (z (u ω))) τ β ()) * (β * Real.log p)) /
        paperPassingCount T L τ β - 4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      condMutualInfo (fun v => φ (z v)) (wordAt (walkLetters z R hstep) L)
        (fun v => ψ (z v)) ((μ).map u) := by
  have hi := smoothedRootPackage_gap_information_lower_bound ν
    (finiteTimeCheckpoint r) b N z R S hstep id
    (by simpa only [id_eq, finiteTimeCheckpoint_val] using hforward)
    (by simpa only [id_eq, finiteTimeCheckpoint_val] using hshift)
    p ρ ψ L f hf hdeg hρ hz T hT hL hlo hhi hsmall τ β hτ hβ herr hβ₁ havoid
  have hfiber (ω : Ω × Fin N) :
      (fun v : Ω × Fin N => finiteTimeCheckpoint r v.1) ⁻¹' {finiteTimeCheckpoint r ω.1} =
      (fun v : Ω × Fin N => r v.1) ⁻¹' {r ω.1} := by
    change Prod.fst ⁻¹' ((finiteTimeCheckpoint r) ⁻¹' {finiteTimeCheckpoint r ω.1}) = _
    rw [finiteTimeCheckpoint_fiber]
    rfl
  simpa only [id_eq, finiteTimeCheckpoint_val, hfiber, exactCheckpointBadEvent,
    mem_deficientCoordinates, ZMod.card] using hi

end Smoothed
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_exact_checkpoint_gap_information_lower_bound
