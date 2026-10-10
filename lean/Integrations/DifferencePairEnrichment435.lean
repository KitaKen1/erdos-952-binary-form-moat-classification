import Integrations.DifferencePairEntropy435
import Integrations.MixedFairEndpoint435
import Integrations.BatchEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Forward
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

/-- One actual mixed experiment supplies the geometric floor, retained prior,
forward-window budget, and fresh fair-mixture inequality. The only quantitative
inputs left here are actual separation failure and the explicit geometric scalar
bound, rather than assumed entropy or fair-mixture inequalities. -/
theorem differencePairForwardLaw_normalized_enrichment
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i)
    (s q D T : ℕ) (hs : 0 < s) (hsq : s < q) (hqk : q ≤ Fintype.card ι)
    (L Lw : ℝ) (hL : 0 < L) (hN : Real.log (N + 1 : ℕ) ≤ Lw)
    (r : A → ℕ) (ε : A → ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
    (hr : ∀ a, μ {a} ≠ 0 → 1 ≤ r a)
    (hsr : ∀ a, μ {a} ≠ 0 → s + r a ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hε : ∀ a, μ {a} ≠ 0 → ε a ≤ 1)
    (herr : ∀ a, μ {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (b a + k)) N)) (r a) ≤ ε a)
    (hnumeric : ∀ a, μ {a} ≠ 0 → L ≤
      ((1 - ε a) * (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r a) :
    (1 + labelledPointEntropyMean K F μ q (fun a => z (b a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean K F
      (fairEndpointLaw (differencePairForwardLaw z N μ b)) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * L) := by
  have hfloor := differencePairForwardLaw_geometric_floor z N μ b K F s D T
    (by omega) r ε L hstep hinj hr hsr hcard hε herr hnumeric
  have hfair := fairEndpointLaw_labelledPointEntropyMean_ge_half
    (differencePairForwardLaw z N μ b)
    (fun ω => z (differencePairFirstTime N b ω))
    (fun ω => z (differencePairSecondTime N b ω)) K F s
  have h := walk_batch_normalized_enrichment K F (differencePairForwardLaw z N μ b)
    (fairEndpointLaw (differencePairForwardLaw z N μ b))
    (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
      (fun ω => z (differencePairSecondTime N b ω))) s q hs hsq hqk z D N hstep
    (fun ω => b ω.1) (differencePairFirstTime N b) (differencePairSecondTime N b)
    (fun ω => (differencePairTimes_bounds N b ω).1)
    (fun ω => (differencePairTimes_bounds N b ω).2.1)
    (fun ω => (differencePairTimes_bounds N b ω).2.2.1)
    (fun ω => (differencePairTimes_bounds N b ω).2.2.2)
    Lw hN T hcard L hL hfloor hfair
  rw [differencePairForwardLaw_labelled_base_entropy z N μ b K F q] at h
  exact h

/-- An earlier original-base checkpoint commutes with the whole pair-plus-coin
experiment, including zero checkpoints. No independence after conditioning on
endpoint residues is asserted. -/
theorem differencePairFairLaw_cond_checkpoint {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : A → B) (c : B) :
    (fairEndpointLaw (differencePairForwardLaw z N μ b))[|
      (fun ω => V ω.1.1) ⁻¹' {c}] =
    fairEndpointLaw (differencePairForwardLaw z N (μ[|V ⁻¹' {c}]) b) := by
  rw [fairEndpointLaw_cond_checkpoint (differencePairForwardLaw z N μ b)
    (fun ω => V ω.1) c, differencePairForwardLaw_cond_checkpoint z N μ b V c]

end Forward
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_normalized_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.differencePairFairLaw_cond_checkpoint
