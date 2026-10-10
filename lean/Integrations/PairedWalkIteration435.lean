import Integrations.PairedWalkProcess435
import Integrations.PairedConditionalEnrichment435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Only a finite prefix of recurrence steps is required. An infinite strictly
decreasing sequence of positive coordinate counts would make an all-n premise vacuous. -/
theorem normalized_enrichment_iterate_prefix (h : ℕ → ℝ) (δ : ℝ) (m : ℕ)
    (hstep : ∀ n < m, (1 + h n) / 2 - δ ≤ h (n + 1)) :
    1 - 2 * δ - ((1 - 2 * δ) - h 0) * (1 / 2 : ℝ) ^ m ≤ h m := by
  induction m with
  | zero => simp only [pow_zero, mul_one]; linarith
  | succ m ih =>
    have hi := ih (fun n hn => hstep n (by omega))
    have hn := hstep m (by omega)
    rw [pow_succ]
    linarith

theorem normalized_enrichment_iterate_prefix_nonneg (h : ℕ → ℝ) (δ : ℝ) (m : ℕ)
    (hδ : 0 ≤ δ) (h0 : 0 ≤ h 0)
    (hstep : ∀ n < m, (1 + h n) / 2 - δ ≤ h (n + 1)) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤ h m := by
  have hi := normalized_enrichment_iterate_prefix h δ m hstep
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
  nlinarith

end BinaryFormMoat.EntropyIntegration
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
  {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i)

/-- One enrichment step applies directly to the recursively constructed law. -/
theorem pairedWalkLaw_enrichment_step (n s q D T : ℕ)
    (hs : 0 < s) (hsq : s < q) (hqk : q ≤ Fintype.card ι)
    (θ L Lw : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hN : Real.log (N n + 1 : ℕ) ≤ Lw)
    (r : PairedWalkSource A N n → ℕ) (ε : PairedWalkSource A N n → ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z)
    (hr : ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → 1 ≤ r a)
    (hsr : ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → s + r a ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hε : ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → ε a ≤ 1)
    (herr : ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (pairedWalkTime N b n a + k)) (N n))) (r a) ≤ ε a)
    (hnumeric : ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → θ * L ≤
      ((1 - ε a) * (Real.log (prefixArea (fun k => z (pairedWalkTime N b n a + k)) (N n) : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r a) :
    (θ + labelledPointEntropyMean K F (pairedWalkLaw z N μ b n) q
      (fun a => z (pairedWalkTime N b n a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean K F (pairedWalkLaw z N μ b (n + 1)) s
      (fun a => z (pairedWalkTime N b (n + 1) a)) / ((s : ℝ) * L) := by
  have h := differencePairForwardLaw_scaled_normalized_enrichment z (N n)
    (pairedWalkLaw z N μ b n) (pairedWalkTime N b n) K F s q D T hs hsq hqk
    θ L Lw hθ hL hN r ε hstep (fun _ _ _ _ _ _ he => Nat.add_left_cancel (hinj he))
    hr hsr hcard hε herr hnumeric
  rw [pairedWalkPoint_step_eq] at h
  exact h

/-- Matched coordinate counts yield a finite entropy-deficit estimate on the
ACTUAL process. The only step hypotheses are explicit geometric and scalar inputs. -/
theorem pairedWalkLaw_enrichment_iterate (m D T : ℕ) (rank : ℕ → ℕ)
    (L δ : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ) (θ Lw : ℕ → ℝ)
    (r : (n : ℕ) → PairedWalkSource A N n → ℕ)
    (ε : (n : ℕ) → PairedWalkSource A N n → ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hrank : ∀ n < m, 0 < rank (n + 1) ∧ rank (n + 1) < rank n ∧ rank n ≤ Fintype.card ι)
    (hθ : ∀ n < m, 0 < θ n)
    (hN : ∀ n < m, Real.log (N n + 1 : ℕ) ≤ Lw n)
    (hr : ∀ n < m, ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → 1 ≤ r n a)
    (hsr : ∀ n < m, ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → rank (n + 1) + r n a ≤ Fintype.card ι)
    (hε : ∀ n < m, ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → ε n a ≤ 1)
    (herr : ∀ n < m, ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (pairedWalkTime N b n a + k)) (N n))) (r n a) ≤ ε n a)
    (hnumeric : ∀ n < m, ∀ a, pairedWalkLaw z N μ b n {a} ≠ 0 → θ n * L ≤
      ((1 - ε n a) * (Real.log (prefixArea (fun k => z (pairedWalkTime N b n a + k)) (N n) : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (rank (n + 1) : ℝ) * Real.log (2 * T : ℕ)) / r n a)
    (herror : ∀ n < m, (1 - θ n) / 2 +
      (4 * Lw n + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (rank (n + 1) : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (rank n - rank (n + 1) : ℕ) * L) ≤ δ) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤
    labelledPointEntropyMean K F (pairedWalkLaw z N μ b m) (rank m)
      (fun a => z (pairedWalkTime N b m a)) / ((rank m : ℝ) * L) := by
  let h := fun n => labelledPointEntropyMean K F (pairedWalkLaw z N μ b n) (rank n)
    (fun a => z (pairedWalkTime N b n a)) / ((rank n : ℝ) * L)
  apply normalized_enrichment_iterate_prefix_nonneg h δ m hδ
  · exact div_nonneg (labelledPointEntropyMean_nonneg K F _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) hL.le)
  · intro n hn
    have hi := pairedWalkLaw_enrichment_step z N μ b K F n (rank (n + 1)) (rank n) D T
      (hrank n hn).1 (hrank n hn).2.1 (hrank n hn).2.2
      (θ n) L (Lw n) (hθ n hn) hL (hN n hn) (r n) (ε n) hstep hinj
      (hr n hn) (hsr n hn) hcard (hε n hn) (herr n hn) (hnumeric n hn)
    have he := herror n hn
    change (θ n + h n) / 2 - _ ≤ h (n + 1) at hi
    linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.EntropyIntegration.normalized_enrichment_iterate_prefix
#print axioms BinaryFormMoat.EntropyIntegration.normalized_enrichment_iterate_prefix_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_enrichment_step
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_enrichment_iterate
