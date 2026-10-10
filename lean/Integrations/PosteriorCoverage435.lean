import Integrations.ResampledCoverage435
import Integrations.PosteriorEntropy435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Posterior
variable {A H J ι R : Type*} [Fintype A] [Fintype H] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Nonempty R]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)
  (G : ι × R → Type*) [∀ c, Fintype (G c)] [∀ c, DecidableEq (G c)]
  [∀ c, MeasurableSpace (G c)] [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddGroup (G c)]
  (y : ∀ c, A → G c) (φ : ∀ c, H → G c)

/-- The posterior sampling construction supplies all trial-law premises.
The conclusion concerns the ORIGINAL terminal law. Coverage hypotheses use
the original exact checkpoint fibers, not separately postulated trial laws.
The geometric joint-entropy and shared-data bounds remain explicit inputs. -/
theorem posterior_one_step_coverage_transfer
    (j₀ : J)
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤
      labelSubsetJointEntropy θ G (fun c ah => y c ah.1) s)
    (hdata : entropy (Prod.snd : A × (J → H) → J → H) (originalResamplingLaw θ h₀) ≤
      κ * (s : ℝ) * coordinateLogMean G)
    (τ δ β β' logT η η' : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) (hβ : 0 ≤ β)
    (hβ' : 0 < β') (hβ'max : β' ≤ 2) (hT : 0 < logT) (hη : 0 ≤ η)
    (hnext : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      ((deficientCoordinates (θ[|Prod.fst ⁻¹' {a}]) G
        (fun c ah => y c ah.1 + φ c ah.2) (τ + 4 * δ) β').card : ℝ) ≤
        η' * Fintype.card (ι × R))
    (hmix : η' ≤ η * δ / 100)
    (hmargin : ∀ c, δ⁻¹ < (Fintype.card (G c) : ℝ) ^ (β' / 2))
    (htail : ∀ c, (Fintype.card (G c) : ℝ) *
      Real.exp (-δ ^ 2 * (Fintype.card J : ℝ) * (Fintype.card (G c) : ℝ) ^ (-β) / 2) ≤ δ / 100)
    (hp : ∀ c, logT ≤ Real.log (Fintype.card (G c)))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β' / 4 * logT)
    (hscale : coordinateLogMean G ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β' / 16) :
    ((deficientCoordinates θ G (fun c ah => y c ah.1 + φ c ah.2) τ β).card : ℝ) /
      (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  have hnxt : ∀ a, (θ.map Prod.fst) {a} ≠ 0 →
      ((deficientCoordinates (originalContinuationLaw θ h₀ a) G
        (fun c h => y c a + φ c h) (τ + 4 * δ) β').card : ℝ) ≤
        η' * Fintype.card (ι × R) := by
    intro a ha
    have ha' : θ (Prod.fst ⁻¹' {a}) ≠ 0 := by
      rwa [Measure.map_apply measurable_fst (MeasurableSet.singleton a)] at ha
    rw [deficientCoordinates_eq_of_identDistrib _ _ G _ _
      (fun c => originalContinuationLaw_cond_identDistrib θ h₀
        (fun ah => y c ah.1 + φ c ah.2) a ha')]
    exact hnext a ha'
  have hj : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤
      labelSubsetJointEntropy (originalResamplingLaw (J := J) θ h₀) G
        (fun c ω => y c ω.1) s := by
    rw [originalResamplingLaw_labelSubsetJointEntropy θ h₀ G y s j₀]
    exact hjoint
  have h := resampled_one_step_coverage_transfer (θ.map Prod.fst) (originalContinuationLaw θ h₀)
    G y φ j₀ s hs hsk ε κ hj hdata τ δ β β' logT η η'
    hτ hτmax hδ hδmax hβ hβ' hβ'max hT hη hnxt hmix hmargin htail hp hlog hscale hcost hbudget
  change ((deficientCoordinates (originalResamplingLaw (J := J) θ h₀) G
    (fun c ω => y c ω.1 + φ c (ω.2 j₀)) τ β).card : ℝ) / _ ≤ η at h
  rw [deficientCoordinates_eq_of_identDistrib _ θ G _ _
    (fun c => originalResamplingLaw_identDistrib θ h₀
      (fun ah => y c ah.1 + φ c ah.2) j₀)] at h
  exact h

end Posterior
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.posterior_one_step_coverage_transfer
