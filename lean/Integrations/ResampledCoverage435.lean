import Integrations.OriginalContinuation435
import Integrations.ConditionalResidues435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Resampled
variable {A H J ι R : Type*} [Fintype A] [Fintype H] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Nonempty R]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (ρ : Measure A) [IsProbabilityMeasure ρ] (ν : A → Measure H)
  [∀ a, IsProbabilityMeasure (ν a)]
  (G : ι × R → Type*) [∀ c, Fintype (G c)] [∀ c, DecidableEq (G c)]
  [∀ c, MeasurableSpace (G c)] [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddGroup (G c)]
  (y : ∀ c, A → G c) (φ : ∀ c, H → G c) (j₀ : J)

/-- The finite resampling experiment discharges common marginals and exact
conditional trial independence. Coverage is assumed for the next terminal
laws y(a)+phi(h), and translated into displacement floors inside the proof. -/
theorem resampled_one_step_coverage_transfer
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤
      labelSubsetJointEntropy (continuationResamplingLaw (J := J) ρ ν) G
        (fun c ω => y c ω.1) s)
    (hdata : entropy (Prod.snd : A × (J → H) → J → H) (continuationResamplingLaw ρ ν) ≤
      κ * (s : ℝ) * coordinateLogMean G)
    (τ δ β β' logT η η' : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) (hβ : 0 ≤ β)
    (hβ' : 0 < β') (hβ'max : β' ≤ 2) (hT : 0 < logT) (hη : 0 ≤ η)
    (hnext : ∀ a, ρ {a} ≠ 0 →
      ((deficientCoordinates (ν a) G (fun c h => y c a + φ c h) (τ + 4 * δ) β').card : ℝ) ≤
        η' * Fintype.card (ι × R))
    (hmix : η' ≤ η * δ / 100)
    (hmargin : ∀ c, δ⁻¹ < (Fintype.card (G c) : ℝ) ^ (β' / 2))
    (htail : ∀ c, (Fintype.card (G c) : ℝ) *
      Real.exp (-δ ^ 2 * (Fintype.card J : ℝ) * (Fintype.card (G c) : ℝ) ^ (-β) / 2) ≤ δ / 100)
    (hp : ∀ c, logT ≤ Real.log (Fintype.card (G c)))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β' / 4 * logT)
    (hscale : coordinateLogMean G ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β' / 16) :
    ((deficientCoordinates (continuationResamplingLaw (J := J) ρ ν) G
      (fun c ω => y c ω.1 + φ c (ω.2 j₀)) τ β).card : ℝ) /
      (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  classical
  have : Nonempty J := ⟨j₀⟩
  let μ := continuationResamplingLaw (J := J) ρ ν
  let good := fun a => (deficientCoordinates (ν a) G
    (fun c h => y c a + φ c h) (τ + 4 * δ) β')ᶜ
  let E := fun a c => lowProbabilityResidues (ν a) (φ c) (τ + 4 * δ)
  have hweight : ∀ a, μ (Prod.fst ⁻¹' {a}) = ρ {a} := continuationResamplingLaw_fiber ρ ν
  apply one_step_coverage_transfer μ Prod.fst measurable_fst G
    (fun c ω => y c ω.1) (fun c ω => y c ω.1 + φ c (ω.2 j₀)) Prod.snd
    (fun _ => measurable_of_finite _) (fun _ => measurable_of_finite _) measurable_snd
    (fun c h j => φ c (h j)) s hs hsk ε κ hjoint hdata good E τ δ β β' logT η η'
    hτ hτmax hδ hδmax hβ hβ' hβ'max hT hη Fintype.card_pos
  · intro c j
    exact (continuationResamplingLaw_identDistrib_trials ρ ν j j₀).comp
      (measurable_of_finite (fun ah : A × H => y c ah.1 + φ c ah.2))
  · intro a ha c _
    exact (continuationResamplingLaw_cond_iIndepFun ρ ν a (by rwa [hweight] at ha)).comp
      (fun _ => φ c) (fun _ => measurable_of_finite _)
  · intro a ha c _ j u hu
    have hfloor : (τ + 4 * δ) / Fintype.card (G c) ≤ (ν a).real ((φ c) ⁻¹' {u}) := by
      exact le_of_not_gt (fun h => hu ((mem_lowProbabilityResidues _ _ _ _).mpr h))
    have ha' : ρ {a} ≠ 0 := by rwa [hweight] at ha
    have hm : (μ[|Prod.fst ⁻¹' {a}]).map (fun ω => φ c (ω.2 j)) = (ν a).map (φ c) := by
      rw [show (fun ω : A × (J → H) => φ c (ω.2 j)) = φ c ∘ (fun ω => ω.2 j) from rfl,
        ← Measure.map_map (measurable_of_finite (φ c)) (measurable_of_finite _)]
      congr 1
      exact continuationResamplingLaw_cond_trial_map ρ ν a ha' j
    have he := congrArg (fun m : Measure (G c) => m.real {u}) hm
    simp only [measureReal_def, Measure.map_apply (measurable_of_finite _)
      (MeasurableSet.singleton u)] at he
    exact hfloor.trans_eq he.symm
  · intro a _ c hc
    have hc' : c ∉ deficientCoordinates (ν a) G
        (fun c h => y c a + φ c h) (τ + 4 * δ) β' := Finset.mem_compl.mp hc
    have hsize := lt_of_not_ge (fun h => hc' ((mem_deficientCoordinates _ _ _ _ _ _).mpr h))
    rw [lowProbabilityResidues_add_const_card] at hsize
    exact hsize
  · intro a ha
    simpa only [good, Finset.compl_eq_univ_sdiff, Finset.sdiff_sdiff_self_left,
      Finset.univ_inter] using hnext a (by rwa [hweight] at ha)
  · exact hmix
  · exact hmargin
  · exact htail
  · exact hp
  · exact hlog
  · exact hscale
  · exact hcost
  · exact hbudget

end Resampled
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.resampled_one_step_coverage_transfer
