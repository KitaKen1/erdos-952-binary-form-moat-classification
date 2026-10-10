import Integrations.PosteriorExactFibers435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Conditional events that agree on the ORIGINAL fiber have identical mass.
This identity includes zero fibers. -/
theorem fiberConditionalReal_congr_on_fiber {Ω A : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (σ : Ω → A) (a : A) (E E' : Set Ω)
    (h : ∀ ω, σ ω = a → (ω ∈ E ↔ ω ∈ E')) :
    fiberConditionalReal μ σ a E = fiberConditionalReal μ σ a E' := by
  have he : σ ⁻¹' {a} ∩ E = σ ⁻¹' {a} ∩ E' := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact and_congr_right (h ω)
  unfold fiberConditionalReal
  simp only [measureReal_def, cond_apply (Set.toFinite _).measurableSet, he]

section Offset
variable {Ω A D G : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [AddGroup G]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
  (N : ℕ) [NeZero N] (V : ℕ → G) (Y : A → G)

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [IsProbabilityMeasure ν] in
/-- The actual relative word uses a fixed target on each exact checkpoint
fiber, while retaining the SAME independent terminal offset. -/
theorem checkpoint_relative_word_hit_exact (a : A) (x : G) (L : ℕ) :
    fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
      (fun ω => σ ω.1) a
      (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun ω => Y (σ ω.1) - x) L) =
      (smoothedTimeLaw (ν[|σ ⁻¹' {a}]) b N).real
        (wordHitSet V id (fun _ => Y a - x) L) := by
  rw [fiberConditionalReal_congr_on_fiber _ _ a _
    (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun _ => Y a - x) L) (by
      intro ω hω
      simp only [wordHitSet, Set.mem_iUnion, wordHitEvent, Set.mem_ofPred_eq, hω])]
  exact independentOffset_cond_wordHit_probability ν σ b N V (Y a - x) L a

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- An ORIGINAL exact-time singleton floor supplies the relative word
floor after smoothing and short-word disjointness. -/
theorem checkpoint_relative_word_hit_half_floor (a : A) (ha : ν (σ ⁻¹' {a}) ≠ 0)
    (x : G) (L : ℕ) (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (δ : ℝ)
    (hfloor : δ ≤ fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
      (fun ω => σ ω.1) a {ω | V (b ω.1 + ω.2.val) = Y a - x})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 ≤ fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
      (fun ω => σ ω.1) a
      (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun ω => Y (σ ω.1) - x) L) := by
  have he := congrArg (fun μ => μ.real {t | V t = Y a - x})
    (smoothedTimeLaw_cond_checkpoint_map ν σ b N a)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet] at he
  have : IsProbabilityMeasure (ν[|σ ⁻¹' {a}]) := cond_isProbabilityMeasure ha
  rw [checkpoint_relative_word_hit_exact]
  exact smoothedTimeLaw_word_hit_half_floor (ν[|σ ⁻¹' {a}]) b N V (Y a - x) L hinj δ
    (hfloor.trans_eq he) herr

omit [Fintype D] in
/-- Coarse CHECKPOINT data mix exact-time relative word floors under the
actual source-times-offset law. Arbitrary future-dependent data are excluded. -/
theorem checkpoint_relative_word_hit_posterior_floor (F : A → D) (d : D)
    (hd : (ν.prod (uniformOn (Set.univ : Set (Fin N)))) ((fun ω => F (σ ω.1)) ⁻¹' {d}) ≠ 0)
    (x : G) (L : ℕ) (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (good : Finset A) (δ u : ℝ) (hδ : 0 ≤ δ)
    (hgood : u ≤ ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
      (fun ω => F (σ ω.1)) ⁻¹' {d}]).real ((fun ω => σ ω.1) ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, ν (σ ⁻¹' {a}) ≠ 0 → F a = d →
      δ ≤ fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
        (fun ω => σ ω.1) a {ω | V (b ω.1 + ω.2.val) = Y a - x})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 * u ≤ fiberConditionalReal
      (ν.prod (uniformOn (Set.univ : Set (Fin N)))) (fun ω => F (σ ω.1)) d
      (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun ω => Y (σ ω.1) - x) L) := by
  apply coarsening_good_exact_floor (ν.prod (uniformOn (Set.univ : Set (Fin N))))
    (fun ω => σ ω.1) F d hd _ good ((L : ℝ) * δ / 2) u (by positivity) hgood
  intro a ha hmass hmatch
  rw [independentOffset_checkpoint_fiber ν σ N a] at hmass
  exact checkpoint_relative_word_hit_half_floor ν σ b N V Y a hmass x L hinj δ
    (hfloor a ha hmass hmatch) herr

end Offset

/-- The actual root-coordinate rejection scale tau*L/(8p), with the original
conditional singleton floors and compatible quarter-mass starts explicit. -/
theorem checkpoint_root_word_hit_posterior_quarter_floor
    {Ω A D : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
    (N : ℕ) [NeZero N] (F : A → D) (d : D)
    (hd : (ν.prod (uniformOn (Set.univ : Set (Fin N)))) ((fun ω => F (σ ω.1)) ⁻¹' {d}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (p : ℕ) (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (Y : A → ZMod p) (x : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (good : Finset A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hgood : (1 : ℝ) / 4 ≤ ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
      (fun ω => F (σ ω.1)) ⁻¹' {d}]).real ((fun ω => σ ω.1) ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, ν (σ ⁻¹' {a}) ≠ 0 → F a = d →
      τ / p ≤ fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
        (fun ω => σ ω.1) a {ω | rootResidueHom p ρ (z (b ω.1 + ω.2.val)) = Y a - x})
    (herr : (L : ℝ) / N ≤ (τ / p) / 2) :
    (L : ℝ) * (τ / p) / 8 ≤ fiberConditionalReal
      (ν.prod (uniformOn (Set.univ : Set (Fin N)))) (fun ω => F (σ ω.1)) d
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) (fun ω => b ω.1 + ω.2.val)
        (fun ω => Y (σ ω.1) - x) L) := by
  convert checkpoint_relative_word_hit_posterior_floor ν σ b N (fun t => rootResidueHom p ρ (z t)) Y F d hd x L
    (fun t => short_word_rootResidues_injective f hf hdeg p ρ hρ z hz R hstep L t hsmall)
    good (τ / p) (1 / 4) (div_nonneg hτ (Nat.cast_nonneg _)) hgood hfloor herr using 1
  ring

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.fiberConditionalReal_congr_on_fiber
#print axioms BinaryFormMoat.EntropyIntegration.checkpoint_relative_word_hit_exact
#print axioms BinaryFormMoat.EntropyIntegration.checkpoint_relative_word_hit_half_floor
#print axioms BinaryFormMoat.EntropyIntegration.checkpoint_relative_word_hit_posterior_floor
#print axioms BinaryFormMoat.EntropyIntegration.checkpoint_root_word_hit_posterior_quarter_floor
