import Integrations.TranslatedCandidates435
import Integrations.CheckpointWordHits435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- ACTUAL favorable root coordinates have at most 4*p^(1-beta) exceptions
and the tau*L/(8p) rejection floor outside them. Original rare sets, candidate
good masses and exact-time singleton floors are all DERIVED, not premises. -/
theorem favorable_root_candidate_rejection
    {Ω A D : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
    (N : ℕ) [NeZero N] (F : A → D) (d : D)
    (hd : (ν.prod (uniformOn (Set.univ : Set (Fin N)))) ((fun ω => F (σ ω.1)) ⁻¹' {d}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (p : ℕ) [NeZero p] (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (Y : A → ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 ≤ τ) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (hbad : fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
      (fun ω => F (σ ω.1)) d
      {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
          (fun ω => σ ω.1) ⁻¹' {σ ω.1}])
        (fun ω => rootResidueHom p ρ (z (b ω.1 + ω.2.val))) τ).card : ℝ)} ≤ (1 : ℝ) / 2) :
    ∃ B : Finset (ZMod p), (B.card : ℝ) ≤ 4 * (p : ℝ) ^ (1 - β) ∧
      ∀ x ∉ B, (L : ℝ) * (τ / p) / 8 ≤ fiberConditionalReal
        (ν.prod (uniformOn (Set.univ : Set (Fin N)))) (fun ω => F (σ ω.1)) d
        (wordHitSet (fun t => rootResidueHom p ρ (z t)) (fun ω => b ω.1 + ω.2.val)
          (fun ω => Y (σ ω.1) - x) L) := by
  let μ := ν.prod (uniformOn (Set.univ : Set (Fin N)))
  let s := fun ω : Ω × Fin N => σ ω.1
  let X := fun ω : Ω × Fin N => rootResidueHom p ρ (z (b ω.1 + ω.2.val))
  let good := singletonCoverageGoodTimes μ s X τ β
  let bad := fun a => translatedCandidateExceptions (μ[|s ⁻¹' {a}]) X (Y a) τ
  let B := Finset.univ.filter (fun x => candidateGoodMass (μ[|(F ∘ s) ⁻¹' {d}]) s good bad x < (1 : ℝ) / 4)
  have hc := posterior_coverage_exceptional_candidates μ s F d hd X Y τ β
    (by simpa only [μ, s, X, Function.comp_def, ZMod.card] using hbad)
  refine ⟨B, by simpa only [ZMod.card] using hc, ?_⟩
  intro x hx
  have hg : (1 : ℝ) / 4 ≤ candidateGoodMass (μ[|(F ∘ s) ⁻¹' {d}]) s good bad x := by
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hx
  exact checkpoint_root_word_hit_posterior_quarter_floor ν σ b N F d hd f hf hdeg p ρ hρ
    z hz R hstep Y x L hsmall (good.filter (fun a => x ∉ bad a)) τ hτ
    (by
      unfold candidateGoodMass at hg
      convert hg using 1
      congr 2
      ext a
      simp only [Finset.mem_coe, Finset.mem_filter]) (by
      intro a ha _ _
      have hn := (Finset.mem_filter.mp ha).2
      simpa only [fiberConditionalReal, μ, s, X, ZMod.card, Set.preimage, Set.mem_singleton_iff, sub_eq_add_neg] using
        translatedCandidateExceptions_floor (μ[|s ⁻¹' {a}]) X (Y a) τ x hn)
    herr

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.favorable_root_candidate_rejection
