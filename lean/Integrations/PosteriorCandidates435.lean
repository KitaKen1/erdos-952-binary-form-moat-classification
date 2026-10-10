import Integrations.PosteriorExactFibers435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Posterior exact-time mass where this candidate has a singleton floor. -/
def candidateGoodMass {Ω A C : Type*} [MeasurableSpace Ω] [Fintype A]
    (ν : Measure Ω) (σ : Ω → A) (good : Finset A) (bad : A → Finset C) (x : C) : ℝ :=
  ν.real (σ ⁻¹' (good.filter (fun a => x ∉ bad a) : Set A))

theorem candidateGoodMass_le {Ω A C : Type*} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Ω) [IsFiniteMeasure ν] (σ : Ω → A)
    (good : Finset A) (bad : A → Finset C) (x : C) :
    candidateGoodMass ν σ good bad x ≤ ν.real (σ ⁻¹' (good : Set A)) := by
  exact measureReal_mono
    (Set.preimage_mono (by intro a ha; exact (Finset.mem_filter.mp ha).1)) (measure_ne_top _ _)

/-- Exact weighted double counting of the candidate deficits. -/
theorem candidateGoodMass_deficit_sum_eq {Ω A C : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype C]
    (ν : Measure Ω) [IsFiniteMeasure ν] (σ : Ω → A) (hσ : Measurable σ)
    (good : Finset A) (bad : A → Finset C) :
    (∑ x, (ν.real (σ ⁻¹' (good : Set A)) - candidateGoodMass ν σ good bad x)) =
      ∑ a ∈ good, ν.real (σ ⁻¹' {a}) * ((bad a).card : ℝ) := by
  have hw := sum_measureReal_preimage_singleton (μ := ν) good
    (fun a _ => hσ (MeasurableSet.singleton a))
  have hu (x : C) : candidateGoodMass ν σ good bad x =
      ∑ a ∈ good, if x ∈ bad a then 0 else ν.real (σ ⁻¹' {a}) := by
    unfold candidateGoodMass
    rw [← sum_measureReal_preimage_singleton _ (fun a _ => hσ (MeasurableSet.singleton a)),
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  simp_rw [← hw, hu, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have he (x : C) : ν.real (σ ⁻¹' {a}) -
      (if x ∈ bad a then 0 else ν.real (σ ⁻¹' {a})) =
      if x ∈ bad a then ν.real (σ ⁻¹' {a}) else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Half posterior good mass leaves at most 4A exceptional candidates.
Only positive exact fibers require cardinal bounds; no independence is used. -/
theorem favorable_exceptional_candidates {Ω A C : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype C]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (hσ : Measurable σ)
    (good : Finset A) (bad : A → Finset C) (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hgood : (1 : ℝ) / 2 ≤ ν.real (σ ⁻¹' (good : Set A)))
    (hbad : ∀ a ∈ good, ν (σ ⁻¹' {a}) ≠ 0 → ((bad a).card : ℝ) ≤ A₀) :
    ((Finset.univ.filter (fun x => candidateGoodMass ν σ good bad x < (1 : ℝ) / 4)).card : ℝ) ≤
      4 * A₀ := by
  apply few_candidates_of_good_mass_deficit (candidateGoodMass ν σ good bad)
    (ν.real (σ ⁻¹' (good : Set A))) A₀ hgood
    (candidateGoodMass_le ν σ good bad)
  rw [candidateGoodMass_deficit_sum_eq ν σ hσ good bad]
  calc
    _ ≤ ∑ a ∈ good, ν.real (σ ⁻¹' {a}) * A₀ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hz : ν (σ ⁻¹' {a}) = 0
      · simp [measureReal_def, hz]
      · exact mul_le_mul_of_nonneg_left (hbad a ha hz) measureReal_nonneg
    _ = ν.real (σ ⁻¹' (good : Set A)) * A₀ := by
      rw [← Finset.sum_mul, sum_measureReal_preimage_singleton good
        (fun a _ => hσ (MeasurableSet.singleton a))]
    _ ≤ A₀ := (mul_le_mul_of_nonneg_right measureReal_le_one hA₀).trans_eq (one_mul _)

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.candidateGoodMass
#print axioms BinaryFormMoat.EntropyIntegration.candidateGoodMass_le
#print axioms BinaryFormMoat.EntropyIntegration.candidateGoodMass_deficit_sum_eq
#print axioms BinaryFormMoat.EntropyIntegration.favorable_exceptional_candidates
