import Integrations.SmoothedRootPackage435
import Integrations.SmoothedRootInformation435
import Integrations.PosteriorBadData435

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

include hforward hshift
/-- Bad ORIGINAL checkpoint-residue branches are now chosen canonically.
Their information cost is DERIVED from twice the original coverage-failure
probability, for ANY additive prior map, with no supplied favorable-data
premise or bad-data budget. Separation, smoothing and forward shift remain
explicit; no positive all-batch rate is asserted. -/
theorem smoothedRootPackage_prior_failure_information_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (havoid : ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    (condEntropy (fun ω => φ (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      Real.log (1 + 5 * (p : ℝ) ^ (1 - β)) -
      2 * (μ).real {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)} * Real.log p) /
        paperPassingCount T L τ β - 4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      condMutualInfo (fun v => φ (z v)) (wordAt (walkLetters z R hstep) L)
        (fun v => ψ (z v)) ((μ).map u) := by
  let V := fun ω : Ω × Fin N => F (σ ω.1)
  let E : Set (Ω × Fin N) := {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
    (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)}
  let bad := posteriorBadData μ V E
  have hi := smoothedRootPackage_information_lower_bound ν σ b N z R S hstep t
    hforward hshift p ρ ψ L f hf hdeg hρ hz T hT hL hlo hhi hsmall τ β hτ hβ herr
    bad (fun a ha _ => posteriorBadData_favorable μ V E a ha) havoid
  have hb := posteriorBadData_mass_le μ V (measurable_of_finite _) E
    (Set.toFinite _).measurableSet
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hc := mul_le_mul_of_nonneg_right hb hl
  have hn : condEntropy (fun ω => φ (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      Real.log (1 + 5 * (p : ℝ) ^ (1 - β)) - 2 * (μ).real E * Real.log p ≤
    condEntropy (fun ω => φ (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      Real.log (1 + 5 * (p : ℝ) ^ (1 - β)) - (μ).real (V ⁻¹' (bad : Set (ZMod p × U))) * Real.log p := by
    linarith
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hn
    (by exact_mod_cast (paperPassingCount_pos T L τ β).le)) _).trans hi

end Smoothed
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_prior_failure_information_lower_bound
