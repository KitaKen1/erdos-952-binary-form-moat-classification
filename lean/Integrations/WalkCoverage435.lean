import Integrations.WalkLaw435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section WalkCoverage
variable {Ω J ι Q : Type*} [Fintype Ω] [Fintype J]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι] [DecidableEq ι] [Fintype Q] [DecidableEq Q] [Nonempty Q]
  [MeasurableSpace Q] [MeasurableSingletonClass Q]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
  (G : ι × Q → Type*) [∀ c, Fintype (G c)] [∀ c, DecidableEq (G c)]
  [∀ c, MeasurableSpace (G c)] [∀ c, MeasurableSingletonClass (G c)]
  [∀ c, AddCommGroup (G c)] (φ : ∀ c, Point →+ G c)
include hstep hforward hshift

/-- A one-step coverage theorem for actual finite random times of any
bounded-step lattice walk. Original conditional laws and original joint
entropy are inputs; posterior trials and the shared-data entropy bound
are derived. The future shift S still needs to be supplied by the schedule. -/
theorem walk_one_step_coverage_transfer (j₀ : J)
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤
      labelSubsetJointEntropy μ G (fun c ω => φ c (z (t ω).val)) s)
    (hdata : (Fintype.card J : ℝ) * (2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ)) ≤
      κ * (s : ℝ) * coordinateLogMean G)
    (τ δ β β' logT η η' : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) (hβ : 0 ≤ β)
    (hβ' : 0 < β') (hβ'max : β' ≤ 2) (hT : 0 < logT) (hη : 0 ≤ η)
    (hnext : ∀ a, μ (t ⁻¹' {a}) ≠ 0 →
      ((deficientCoordinates (μ[|t ⁻¹' {a}]) G
        (fun c ω => φ c (z (u ω))) (τ + 4 * δ) β').card : ℝ) ≤
          η' * Fintype.card (ι × Q))
    (hmix : η' ≤ η * δ / 100)
    (hmargin : ∀ c, δ⁻¹ < (Fintype.card (G c) : ℝ) ^ (β' / 2))
    (htail : ∀ c, (Fintype.card (G c) : ℝ) *
      Real.exp (-δ ^ 2 * (Fintype.card J : ℝ) * (Fintype.card (G c) : ℝ) ^ (-β) / 2) ≤ δ / 100)
    (hp : ∀ c, logT ≤ Real.log (Fintype.card (G c)))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β' / 4 * logT)
    (hscale : coordinateLogMean G ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β' / 16) :
    ((deficientCoordinates μ G (fun c ω => φ c (z (u ω))) τ β).card : ℝ) /
      (Fintype.card ι * (Fintype.card Q : ℝ)) ≤ η := by
  let θ := walkCheckpointLaw μ z R S hstep t u hforward hshift
  let y := fun c (a : Fin M) => φ c (z a.val)
  let ψ := fun c (h : BoundedDisplacement ((R + 1) * S)) => φ c h.val
  have hj : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤
      labelSubsetJointEntropy θ G (fun c ah => y c ah.1) s := by
    rw [walkCheckpointLaw_labelSubsetJointEntropy μ z R S hstep t u hforward hshift]
    exact hjoint
  have hd : entropy (Prod.snd : Fin M × (J → BoundedDisplacement ((R + 1) * S)) →
      J → BoundedDisplacement ((R + 1) * S))
      (originalResamplingLaw θ (zeroDisplacement ((R + 1) * S))) ≤
        κ * (s : ℝ) * coordinateLogMean G :=
    (walk_resampled_data_entropy_le μ z R S hstep t u hforward hshift).trans hdata
  have hn : ∀ a, θ (Prod.fst ⁻¹' {a}) ≠ 0 →
      ((deficientCoordinates (θ[|Prod.fst ⁻¹' {a}]) G
        (fun c ah => y c ah.1 + ψ c ah.2) (τ + 4 * δ) β').card : ℝ) ≤
          η' * Fintype.card (ι × Q) := by
    intro a ha
    have hw : θ (Prod.fst ⁻¹' {a}) = μ (t ⁻¹' {a}) :=
      finiteCheckpointLaw_fiber μ t (walkDisplacement z R S hstep t u hforward hshift) a
    rw [deficientCoordinates_eq_of_identDistrib _ _ G _ _
      (fun c => walkCheckpointLaw_cond_terminal_identDistrib μ z R S hstep t u
        hforward hshift (φ c) a)]
    exact hnext a (by rwa [hw] at ha)
  have h := posterior_one_step_coverage_transfer θ (zeroDisplacement ((R + 1) * S))
    G y ψ j₀ s hs hsk ε κ hj hd τ δ β β' logT η η'
    hτ hτmax hδ hδmax hβ hβ' hβ'max hT hη hn hmix hmargin htail hp hlog hscale hcost hbudget
  rw [deficientCoordinates_eq_of_identDistrib _ _ G _ _
    (fun c => walkCheckpointLaw_terminal_identDistrib μ z R S hstep t u
      hforward hshift (φ c))] at h
  exact h

end WalkCoverage
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.walk_one_step_coverage_transfer
