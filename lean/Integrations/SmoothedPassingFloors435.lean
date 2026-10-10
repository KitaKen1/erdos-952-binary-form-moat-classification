import Integrations.SmoothedWordHits435
import Integrations.ConditionalAverage435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Average favorable exact fibers; zero-mass fibers contribute zero. -/
theorem measureReal_ge_good_fiber_floor {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → A) (hV : Measurable V)
    (E : Set Ω) (hE : MeasurableSet E) (good : Finset A) (r : ℝ)
    (hfloor : ∀ a ∈ good, μ (V ⁻¹' {a}) ≠ 0 → r ≤ fiberConditionalReal μ V a E) :
    r * μ.real (V ⁻¹' (good : Set A)) ≤ μ.real E := by
  classical
  have hw := sum_measureReal_preimage_singleton (μ := μ) good
    (fun a _ => hV (MeasurableSet.singleton a))
  rw [measureReal_eq_sum_fiberConditionalReal μ V hV E hE]
  calc
    _ = ∑ a ∈ good, μ.real (V ⁻¹' {a}) * r := by
      rw [← hw, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ ∑ a ∈ good, μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a E := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hz : μ (V ⁻¹' {a}) = 0
      · simp [measureReal_def, hz]
      · exact mul_le_mul_of_nonneg_left (hfloor a ha hz) measureReal_nonneg
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun _ _ _ => mul_nonneg measureReal_nonneg (by
        unfold fiberConditionalReal
        exact measureReal_nonneg))

/-- The independent offset preserves each earlier-checkpoint mass. -/
theorem independentOffset_checkpoint_fiber {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (σ : Ω → A) (N : ℕ) [NeZero N] (a : A) :
    (μ.prod (uniformOn (Set.univ : Set (Fin N))))
      ((fun ω => σ ω.1) ⁻¹' {a}) = μ (σ ⁻¹' {a}) := by
  have he : (fun ω : Ω × Fin N => σ ω.1) ⁻¹' {a} = (σ ⁻¹' {a}) ×ˢ Set.univ := by
    ext ω
    simp
  rw [he, Measure.prod_prod, measure_univ, mul_one]

section FiniteSource
variable {Ω A : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → A) (b : Ω → ℕ)
  (N : ℕ) [NeZero N]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [IsProbabilityMeasure μ] in
/-- A fixed candidate under the earlier fiber uses exactly the smoothed
source law. The target is fixed after conditioning, not re-randomized. -/
theorem independentOffset_cond_wordHit_probability {G : Type*}
    (V : ℕ → G) (c : G) (L : ℕ) (a : A) :
    ((μ.prod (uniformOn (Set.univ : Set (Fin N))))[|(fun ω => σ ω.1) ⁻¹' {a}]).real
      (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun _ => c) L) =
    (smoothedTimeLaw (μ[|σ ⁻¹' {a}]) b N).real (wordHitSet V id (fun _ => c) L) := by
  have h := congrArg (fun ν : Measure ℕ => ν.real (wordHitSet V id (fun _ => c) L))
    (smoothedTimeLaw_cond_checkpoint_map μ σ b N a)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet] at h
  convert h using 1
  congr 1
  ext ω
  simp [wordHitSet, wordHitEvent]

/-- Good singleton floors, smoothing and disjoint word hits yield an
unconditional floor on the actual source-times-offset package law. -/
theorem smoothedTimeLaw_word_hit_floor_of_good_fibers {G : Type*}
    (V : ℕ → G) (c : G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (good : Finset A) (δ u : ℝ) (hδ : 0 ≤ δ)
    (hgood : u ≤ μ.real (σ ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, μ (σ ⁻¹' {a}) ≠ 0 →
      δ ≤ (smoothedTimeLaw (μ[|σ ⁻¹' {a}]) b N).real {t | V t = c})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 * u ≤ (μ.prod (uniformOn (Set.univ : Set (Fin N)))).real
      (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun _ => c) L) := by
  have hm : (μ.prod (uniformOn (Set.univ : Set (Fin N)))).real
      ((fun ω => σ ω.1) ⁻¹' (good : Set A)) = μ.real (σ ⁻¹' (good : Set A)) := by
    have he : (fun ω : Ω × Fin N => σ ω.1) ⁻¹' (good : Set A) =
        (σ ⁻¹' (good : Set A)) ×ˢ Set.univ := by
      ext ω
      simp
    simp only [measureReal_def, he, Measure.prod_prod, measure_univ, mul_one]
  have hf := measureReal_ge_good_fiber_floor
    (μ.prod (uniformOn (Set.univ : Set (Fin N)))) (fun ω => σ ω.1)
    (measurable_of_finite _) (wordHitSet V (fun ω => b ω.1 + ω.2.val) (fun _ => c) L)
    (Set.toFinite _).measurableSet good ((L : ℝ) * δ / 2) (by
      intro a ha hz
      have hz' : μ (σ ⁻¹' {a}) ≠ 0 := by
        rwa [independentOffset_checkpoint_fiber] at hz
      have : IsProbabilityMeasure (μ[|σ ⁻¹' {a}]) := cond_isProbabilityMeasure hz'
      unfold fiberConditionalReal
      rw [independentOffset_cond_wordHit_probability]
      exact smoothedTimeLaw_word_hit_half_floor (μ[|σ ⁻¹' {a}]) b N V c L hinj δ
        (hfloor a ha hz') herr)
  rw [hm] at hf
  exact (mul_le_mul_of_nonneg_left hgood (by positivity : 0 ≤ (L : ℝ) * δ / 2)).trans hf

theorem smoothedTimeLaw_root_word_hit_floor_of_good_fibers (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (good : Finset A) (δ u : ℝ) (hδ : 0 ≤ δ)
    (hgood : u ≤ μ.real (σ ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, μ (σ ⁻¹' {a}) ≠ 0 →
      δ ≤ (smoothedTimeLaw (μ[|σ ⁻¹' {a}]) b N).real {t | rootResidueHom p ρ (z t) = c})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 * u ≤ (μ.prod (uniformOn (Set.univ : Set (Fin N)))).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t))
        (fun ω => b ω.1 + ω.2.val) (fun _ => c) L) := by
  exact smoothedTimeLaw_word_hit_floor_of_good_fibers μ σ b N _ c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall)
    good δ u hδ hgood hfloor herr

/-- The source's quarter-mass good fibers give the tau*L/(8*p) scale.
Both the singleton floor and good mass remain explicit geometric inputs. -/
theorem smoothedTimeLaw_root_word_hit_quarter_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (good : Finset A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hgood : (1 : ℝ) / 4 ≤ μ.real (σ ⁻¹' (good : Set A)))
    (hfloor : ∀ a ∈ good, μ (σ ⁻¹' {a}) ≠ 0 →
      τ / p ≤ (smoothedTimeLaw (μ[|σ ⁻¹' {a}]) b N).real
        {t | rootResidueHom p ρ (z t) = c})
    (herr : (L : ℝ) / N ≤ (τ / p) / 2) :
    (L : ℝ) * (τ / p) / 8 ≤ (μ.prod (uniformOn (Set.univ : Set (Fin N)))).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t))
        (fun ω => b ω.1 + ω.2.val) (fun _ => c) L) := by
  convert smoothedTimeLaw_root_word_hit_floor_of_good_fibers μ σ b N f hf hd p ρ hρ
    z hz R hstep c L hsmall good (τ / p) (1 / 4)
    (div_nonneg hτ (Nat.cast_nonneg p)) hgood hfloor herr using 1
  ring

end FiniteSource

/-- A supplied summed deficit yields the source's 4A exceptional-candidate
bound, without fractional powers or probabilistic independence. -/
theorem few_candidates_of_good_mass_deficit {C : Type*} [Fintype C]
    (u : C → ℝ) (g A : ℝ) (hg : (1 : ℝ) / 2 ≤ g)
    (hu : ∀ x, u x ≤ g) (hbudget : (∑ x, (g - u x)) ≤ A) :
    ((Finset.univ.filter (fun x => u x < (1 : ℝ) / 4)).card : ℝ) ≤ 4 * A := by
  classical
  let B := Finset.univ.filter (fun x => u x < (1 : ℝ) / 4)
  have hb : (B.card : ℝ) / 4 ≤ ∑ x ∈ B, (g - u x) := by
    calc
      _ = ∑ _ ∈ B, (1 : ℝ) / 4 := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => by
        have hx' : u x < (1 : ℝ) / 4 := (Finset.mem_filter.mp hx).2
        linarith)
  have hs : (∑ x ∈ B, (g - u x)) ≤ ∑ x, (g - u x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun x _ _ => sub_nonneg.mpr (hu x))
  change (B.card : ℝ) ≤ 4 * A
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.measureReal_ge_good_fiber_floor
#print axioms BinaryFormMoat.EntropyIntegration.independentOffset_checkpoint_fiber
#print axioms BinaryFormMoat.EntropyIntegration.independentOffset_cond_wordHit_probability
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_hit_floor_of_good_fibers
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_hit_floor_of_good_fibers
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_hit_quarter_floor
#print axioms BinaryFormMoat.EntropyIntegration.few_candidates_of_good_mass_deficit
