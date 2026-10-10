import Integrations.ShortWordResidues435
import Mathlib.MeasureTheory.Measure.Real

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory

/-- An actual offset hit, with arbitrary random start and target. -/
def wordHitEvent {Ω G : Type*} (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G)
    {L : ℕ} (i : Fin L) : Set Ω := {ω | V (a ω + i) = c ω}

def wordHitSet {Ω G : Type*} (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G)
    (L : ℕ) : Set Ω := ⋃ i : Fin L, wordHitEvent V a c i

theorem wordHitEvent_pairwise_disjoint {Ω G : Type*}
    (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i))) :
    Pairwise (fun i j : Fin L => Disjoint (wordHitEvent V a c i) (wordHitEvent V a c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hij (hinj (a ω) (hi.trans hj.symm))

section CountableSource
variable {Ω G : Type*} [Countable Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

theorem measurableSet_wordHitEvent (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G)
    {L : ℕ} (i : Fin L) : MeasurableSet (wordHitEvent V a c i) :=
  (Set.to_countable _).measurableSet

/-- Disjointness, not independence, gives the exact length gain. -/
theorem wordHit_probability_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i))) :
    μ.real (wordHitSet V a c L) = ∑ i : Fin L, μ.real (wordHitEvent V a c i) := by
  exact measureReal_iUnion_fintype (wordHitEvent_pairwise_disjoint V a c L hinj)
    (measurableSet_wordHitEvent V a c)

theorem wordHit_probability_ge_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (δ : Fin L → ℝ) (hδ : ∀ i, δ i ≤ μ.real (wordHitEvent V a c i)) :
    ∑ i, δ i ≤ μ.real (wordHitSet V a c L) := by
  rw [wordHit_probability_eq_sum μ V a c L hinj]
  exact Finset.sum_le_sum (fun i _ => hδ i)

theorem wordHit_probability_ge_length_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    (V : ℕ → G) (a : Ω → ℕ) (c : Ω → G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (δ : ℝ) (hδ : ∀ i : Fin L, δ ≤ μ.real (wordHitEvent V a c i)) :
    (L : ℝ) * δ ≤ μ.real (wordHitSet V a c L) := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    wordHit_probability_ge_sum μ V a c L hinj (fun _ => δ) hδ

/-- The integer-polynomial short-word bound applies to the actual law of
random starts and candidate targets, without primitivity or independence. -/
theorem short_word_root_hit_probability_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (p : ℕ) (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (a : Ω → ℕ) (c : Ω → ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p) :
    μ.real (wordHitSet (fun t => rootResidueHom p ρ (z t)) a c L) =
      ∑ i : Fin L, μ.real (wordHitEvent (fun t => rootResidueHom p ρ (z t)) a c i) := by
  exact wordHit_probability_eq_sum μ _ a c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall)

theorem short_word_root_hit_probability_ge (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (p : ℕ) (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (a : Ω → ℕ) (c : Ω → ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (δ : ℝ)
    (hδ : ∀ i : Fin L, δ ≤
      μ.real (wordHitEvent (fun t => rootResidueHom p ρ (z t)) a c i)) :
    (L : ℝ) * δ ≤ μ.real (wordHitSet (fun t => rootResidueHom p ρ (z t)) a c L) := by
  exact wordHit_probability_ge_length_mul μ _ a c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall) δ hδ

end CountableSource
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.wordHitEvent_pairwise_disjoint
#print axioms BinaryFormMoat.EntropyIntegration.measurableSet_wordHitEvent
#print axioms BinaryFormMoat.EntropyIntegration.wordHit_probability_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.wordHit_probability_ge_sum
#print axioms BinaryFormMoat.EntropyIntegration.wordHit_probability_ge_length_mul
#print axioms BinaryFormMoat.EntropyIntegration.short_word_root_hit_probability_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.short_word_root_hit_probability_ge
