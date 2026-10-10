import Integrations.DifferencePairEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Normalize at the TRUE prime-log scale even when the geometric floor
retains only a factor theta of it. -/
theorem normalized_enrichment_rescale (s q : ℕ) (hs : 0 < s) (hsq : s < q)
    (θ L H W C : ℝ) (hθ : 0 < θ) (hL : 0 < L)
    (h : (1 + H / ((q : ℝ) * (θ * L))) / 2 -
      C / (2 * (q - s : ℕ) * (θ * L)) ≤ W / ((s : ℝ) * (θ * L))) :
    (θ + H / ((q : ℝ) * L)) / 2 - C / (2 * (q - s : ℕ) * L) ≤
      W / ((s : ℝ) * L) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : 0 < q).ne'
  have hd0 : ((q - s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hsq).ne'
  have hm := mul_le_mul_of_nonneg_left h hθ.le
  convert hm using 1 <;> field_simp

/-- Conditioning cannot create a positive singleton outside the original support. -/
theorem cond_singleton_ne_zero_imp {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) (E : Set A) (a : A)
    (ha : μ[|E] {a} ≠ 0) : μ {a} ≠ 0 := by
  intro hz
  have hi : μ (E ∩ {a}) = 0 := le_antisymm (by simpa [hz] using
    (measure_mono (Set.inter_subset_right : E ∩ {a} ⊆ {a}) : μ (E ∩ {a}) ≤ μ {a})) bot_le
  apply ha
  rw [cond_apply' (MeasurableSet.singleton a), hi, mul_zero]

section Forward
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

/-- Actual paired enrichment with an explicit fractional geometric floor,
keeping the TRUE normalization scale for matching successive transitions. -/
theorem differencePairForwardLaw_scaled_normalized_enrichment
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i)
    (s q D T : ℕ) (hs : 0 < s) (hsq : s < q) (hqk : q ≤ Fintype.card ι)
    (θ L Lw : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hN : Real.log (N + 1 : ℕ) ≤ Lw)
    (r : A → ℕ) (ε : A → ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
    (hr : ∀ a, μ {a} ≠ 0 → 1 ≤ r a)
    (hsr : ∀ a, μ {a} ≠ 0 → s + r a ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hε : ∀ a, μ {a} ≠ 0 → ε a ≤ 1)
    (herr : ∀ a, μ {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (b a + k)) N)) (r a) ≤ ε a)
    (hnumeric : ∀ a, μ {a} ≠ 0 → θ * L ≤
      ((1 - ε a) * (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r a) :
    (θ + labelledPointEntropyMean K F μ q (fun a => z (b a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean K F
      (fairEndpointLaw (differencePairForwardLaw z N μ b)) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * L) := by
  have h := differencePairForwardLaw_normalized_enrichment z N μ b K F s q D T
    (by omega) hsq hqk (θ * L) Lw (mul_pos hθ hL) hN r ε hstep hinj hr hsr
    hcard hε herr hnumeric
  exact normalized_enrichment_rescale s q hs hsq θ L _ _ _ hθ hL h

/-- Positive earlier-base checkpoints use the actual conditioned pair-plus-coin
law. All support-sensitive geometric inputs come from the ORIGINAL base support. -/
theorem differencePairFairLaw_cond_scaled_normalized_enrichment
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : A → B) (c : B) (hc : μ (V ⁻¹' {c}) ≠ 0)
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i)
    (s q D T : ℕ) (hs : 0 < s) (hsq : s < q) (hqk : q ≤ Fintype.card ι)
    (θ L Lw : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hN : Real.log (N + 1 : ℕ) ≤ Lw)
    (r : A → ℕ) (ε : A → ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
    (hr : ∀ a, μ {a} ≠ 0 → 1 ≤ r a)
    (hsr : ∀ a, μ {a} ≠ 0 → s + r a ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hε : ∀ a, μ {a} ≠ 0 → ε a ≤ 1)
    (herr : ∀ a, μ {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (b a + k)) N)) (r a) ≤ ε a)
    (hnumeric : ∀ a, μ {a} ≠ 0 → θ * L ≤
      ((1 - ε a) * (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r a) :
    (θ + labelledPointEntropyMean K F (μ[|V ⁻¹' {c}]) q (fun a => z (b a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean K F
      ((fairEndpointLaw (differencePairForwardLaw z N μ b))[|(fun ω => V ω.1.1) ⁻¹' {c}]) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * L) := by
  let := cond_isProbabilityMeasure (μ := μ) (s := V ⁻¹' {c}) hc
  rw [differencePairFairLaw_cond_checkpoint z N μ b V c]
  apply differencePairForwardLaw_scaled_normalized_enrichment z N (μ[|V ⁻¹' {c}]) b
    K F s q D T hs hsq hqk θ L Lw hθ hL hN r ε hstep
  · intro a ha
    exact hinj a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hr a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hsr a (cond_singleton_ne_zero_imp μ _ a ha)
  · exact hcard
  · intro a ha
    exact hε a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact herr a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hnumeric a (cond_singleton_ne_zero_imp μ _ a ha)

end Forward
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.normalized_enrichment_rescale
#print axioms BinaryFormMoat.GeometryIntegration.cond_singleton_ne_zero_imp
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_scaled_normalized_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.differencePairFairLaw_cond_scaled_normalized_enrichment
