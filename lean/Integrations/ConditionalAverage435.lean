import Integrations.CoverageBudget435
import Mathlib.Probability.ConditionalProbability

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def fiberConditionalReal {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → A) (a : A) (E : Set Ω) : ℝ :=
  (μ[|V ⁻¹' {a}]).real E

/-- Zero-mass fibers contribute zero, without a probability instance on them. -/
theorem fiberConditionalReal_mul_weight {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → A) (hV : Measurable V)
    (a : A) (E : Set Ω) :
    fiberConditionalReal μ V a E * μ.real (V ⁻¹' {a}) = μ.real (V ⁻¹' {a} ∩ E) := by
  unfold fiberConditionalReal
  simpa only [measureReal_def, ENNReal.toReal_mul] using
    congrArg ENNReal.toReal (cond_mul_eq_inter (hV (MeasurableSet.singleton a)) E μ)

theorem measureReal_eq_sum_fiberConditionalReal {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → A) (hV : Measurable V)
    (E : Set Ω) (hE : MeasurableSet E) :
    μ.real E = ∑ a, μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a E := by
  have hp : Pairwise (fun a b => Disjoint (V ⁻¹' {a} ∩ E) (V ⁻¹' {b} ∩ E)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    have ha' : V ω = a := ha.1
    have hb' : V ω = b := hb.1
    exact hab (ha'.symm.trans hb')
  have he : (⋃ a, V ⁻¹' {a} ∩ E) = E := by
    ext ω
    simp
  have hm := measureReal_iUnion_fintype (μ := μ) hp
    (fun a => (hV (MeasurableSet.singleton a)).inter hE)
  rw [he] at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm, fiberConditionalReal_mul_weight μ V hV a]

theorem fiber_weights_sum_one {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V) :
    ∑ a, μ.real (V ⁻¹' {a}) = 1 := by
  simpa using sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (fun a _ => hV (MeasurableSet.singleton a))

theorem fiberConditionalReal_le_one {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → A) (a : A) (E : Set Ω) :
    fiberConditionalReal μ V a E ≤ 1 := by
  by_cases ha : μ (V ⁻¹' {a}) = 0
  · simp [fiberConditionalReal, cond_eq_zero_of_meas_eq_zero ha]
  · have := cond_isProbabilityMeasure (μ := μ) ha
    exact (measureReal_mono (μ := μ[|V ⁻¹' {a}]) (Set.subset_univ E)).trans_eq probReal_univ

/-- Average exact conditional failures, then restrict to any nonempty set
of coordinates. The bad coordinate sets may depend on the mixing value. -/
theorem mean_probability_le_of_fiber_coverage {Ω A C : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype C] [DecidableEq C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V)
    (B : Finset C) (hB : B.Nonempty) (good : A → Finset C)
    (E : C → Set Ω) (hE : ∀ c, MeasurableSet (E c)) (b η' : ℝ) (hb : 0 ≤ b)
    (hgood : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      fiberConditionalReal μ V a (E c) ≤ b)
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 →
      ((Finset.univ \ good a).card : ℝ) ≤ η' * Fintype.card C) :
    finiteRealMean B (fun c => μ.real (E c)) ≤
      b + η' * Fintype.card C / B.card := by
  classical
  have hn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hw : ∀ a, μ.real (V ⁻¹' {a}) *
      (∑ c ∈ B, fiberConditionalReal μ V a (E c)) ≤
      μ.real (V ⁻¹' {a}) * (b * B.card + η' * Fintype.card C) := by
    intro a
    by_cases ha : μ (V ⁻¹' {a}) = 0
    · simp [measureReal_def, ha]
    · apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      calc
        _ ≤ ∑ c ∈ B, (b + if c ∈ good a then 0 else (1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : c ∈ good a
          · simpa [hc] using hgood a ha c hc
          · simpa [hc] using (fiberConditionalReal_le_one μ V a (E c)).trans
              (by linarith : (1 : ℝ) ≤ b + 1)
        _ = b * B.card + ((B \ good a).card : ℝ) := by
          simp [Finset.sum_add_distrib, Finset.sdiff_eq_filter, ← Finset.sum_boole, mul_comm]
        _ ≤ _ := add_le_add le_rfl ((by exact_mod_cast
          (Finset.card_le_card (show B \ good a ⊆ Finset.univ \ good a from
            Finset.sdiff_subset_sdiff (Finset.subset_univ B) (Finset.Subset.refl _))) :
          ((B \ good a).card : ℝ) ≤ (Finset.univ \ good a).card).trans (hbad a ha))
  have hs : ∑ c ∈ B, μ.real (E c) ≤ b * B.card + η' * Fintype.card C := by
    simp_rw [measureReal_eq_sum_fiberConditionalReal μ V hV _ (hE _)]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    apply (Finset.sum_le_sum (fun a _ => hw a)).trans_eq
    rw [← Finset.sum_mul, fiber_weights_sum_one μ V hV, one_mul]
  unfold finiteRealMean
  apply (div_le_iff₀ hn).mpr
  convert hs using 1
  field_simp

/-- The source budget eta' <= eta*delta/100 absorbs both the conditional
tail delta/100 and the fraction of uncovered coordinates. -/
theorem mean_probability_le_coverage_budget {Ω A C : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype C] [DecidableEq C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V)
    (B : Finset C) (hB : B.Nonempty) (good : A → Finset C)
    (E : C → Set Ω) (hE : ∀ c, MeasurableSet (E c)) (δ η η' : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      fiberConditionalReal μ V a (E c) ≤ δ / 100)
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 →
      ((Finset.univ \ good a).card : ℝ) ≤ η' * Fintype.card C)
    (hθ : η ≤ (B.card : ℝ) / Fintype.card C) (hbudget : η' ≤ η * δ / 100) :
    finiteRealMean B (fun c => μ.real (E c)) ≤ δ / 50 := by
  have hn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hC : (0 : ℝ) < Fintype.card C := by
    rcases hB with ⟨c, _⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨c⟩)
  have hθ' := (le_div_iff₀ hC).mp hθ
  have hb := mul_le_mul_of_nonneg_right hbudget hC.le
  have hc := mul_le_mul_of_nonneg_right hθ' (div_nonneg hδ (by norm_num : (0 : ℝ) ≤ 100))
  have he : η' * (Fintype.card C : ℝ) / B.card ≤ δ / 100 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith only [hb, hc]
  have h := mean_probability_le_of_fiber_coverage μ V hV B hB good E hE
    (δ / 100) η' (div_nonneg hδ (by norm_num)) hgood hbad
  linarith only [h, he]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.fiberConditionalReal_mul_weight
#print axioms BinaryFormMoat.EntropyIntegration.measureReal_eq_sum_fiberConditionalReal
#print axioms BinaryFormMoat.EntropyIntegration.fiber_weights_sum_one
#print axioms BinaryFormMoat.EntropyIntegration.fiberConditionalReal_le_one
#print axioms BinaryFormMoat.EntropyIntegration.mean_probability_le_of_fiber_coverage
#print axioms BinaryFormMoat.EntropyIntegration.mean_probability_le_coverage_budget
