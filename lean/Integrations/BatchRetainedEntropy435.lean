import Integrations.WalkEnrichmentCost435
import Integrations.RemainingCoordinate435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Source
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
  [∀ i, MeasurableSingletonClass (K i)]

/-- Keep a specified outer tuple, deleting only coordinates actually known
from the observation. No extension to the full global tuple is needed. -/
theorem entropy_subset_sub_observation_le_remaining {O : Type*}
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (X : ∀ i, Ω → K i) (Obs : Ω → O) (Q S : Finset ι)
    (hknown : ∀ i ∈ S, ∃ f : O → K i, ∀ ω, X i ω = f (Obs ω)) :
    subsetEntropy K μ X Q - entropy Obs μ ≤
      ∑ i ∈ Q \ S, condEntropy (X i) Obs μ := by
  classical
  have hz (i : ι) (hi : i ∈ S) : condEntropy (X i) Obs μ = 0 := by
    obtain ⟨f, hf⟩ := hknown i hi
    have he : X i = f ∘ Obs := funext hf
    rw [he]
    exact condEntropy_of_function_eq_zero_finite μ Obs f
  have hs : (∑ i ∈ Q \ S, condEntropy (X i) Obs μ) = ∑ i ∈ Q, condEntropy (X i) Obs μ := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro i hi hn
    exact hz i (by simpa only [Finset.mem_sdiff, hi, true_and, not_not] using hn)
  rw [hs]
  exact (entropy_sub_observation_le_condEntropy_finite μ (subsetObservation K X Q) Obs).trans
    (condEntropy_subsetObservation_le_sum μ K X (fun _ => measurable_of_finite _)
      Obs (measurable_of_finite _) Q)

section Points
variable [Fintype ι] [∀ i, AddCommGroup (K i)] (F : ∀ i, Point →+ K i)

/-- Starting outer-batch entropy is retained on the original common source. -/
theorem walk_subset_remaining_prior_lower_bound (Q S : Finset ι) (X Y Z : Ω → Point) :
    subsetEntropy K μ (fun i ω => F i (Z ω)) Q - entropy (fun ω => X ω - Z ω) μ -
      entropy (fun ω => X ω - Y ω) μ - 2 * (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
      ∑ i ∈ Q \ S, condEntropy (fun ω => F i (X ω))
        (residueDifferenceObservation K F S X Y) μ := by
  classical
  let Bx := residuePrefix K F S X
  let By := residuePrefix K F S Y
  let O := residueDifferenceObservation K F S X Y
  let FQ : Point →+ ((i : Q) → K i.val) :=
    { toFun := fun x i => F i.val x
      map_zero' := by ext i; exact map_zero _
      map_add' := by intro x y; ext i; exact map_add _ _ _ }
  have hr := entropy_subset_sub_observation_le_remaining μ K (fun i ω => F i (X ω)) O Q S (by
    intro i hi
    exact ⟨fun o => o.2.1 ⟨i, hi⟩, fun _ => rfl⟩)
  have hp := entropy_projection_prior_ge_sub_displacement μ FQ X Z
  change subsetEntropy K μ (fun i ω => F i (Z ω)) Q - entropy (fun ω => X ω - Z ω) μ ≤
    subsetEntropy K μ (fun i ω => F i (X ω)) Q at hp
  have ho := entropy_pair_le_add (measurable_of_finite (fun ω => X ω - Y ω))
    (measurable_of_finite (fun ω => (Bx ω, By ω))) μ
  change entropy O μ ≤ _ at ho
  have hb := entropy_pair_le_add (measurable_of_finite Bx) (measurable_of_finite By) μ
  have hx := residuePrefix_entropy_le_log_card_sum K μ F S X
  have hy := residuePrefix_entropy_le_log_card_sum K μ F S Y
  change entropy Bx μ ≤ _ at hx
  change entropy By μ ≤ _ at hy
  linarith

/-- The same physical difference is retained while summing only the fresh
coordinates of the chosen outer batch. -/
theorem sum_subset_difference_and_prior_le_endpoints (Q S : Finset ι) (X Y : Ω → Point) :
    (∑ i ∈ Q \ S, condEntropy (fun ω => F i (X ω - Y ω))
      (fun ω => (residuePrefix K F S X ω, residuePrefix K F S Y ω)) μ) +
    (∑ i ∈ Q \ S, condEntropy (fun ω => F i (X ω))
      (residueDifferenceObservation K F S X Y) μ) ≤
    ∑ i ∈ Q \ S, (condEntropy (fun ω => F i (X ω)) (residuePrefix K F S X) μ +
      condEntropy (fun ω => F i (Y ω)) (residuePrefix K F S Y) μ) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := condEntropy_difference_retains_full_data μ
    (fun ω => F i (X ω)) (fun ω => F i (Y ω)) (fun ω => X ω - Y ω) (F i)
    (residuePrefix K F S X) (residuePrefix K F S Y) (fun _ => (map_sub (F i) _ _).symm)
  change _ + condEntropy (fun ω => F i (X ω))
    (residueDifferenceObservation K F S X Y) μ ≤ _ at h
  simpa only [map_sub] using h

/-- No pointwise geometric floor is assumed for an individual outer batch. -/
theorem walk_subset_retained_enrichment_budget (Q S : Finset ι) (X Y Z : Ω → Point) :
    (∑ i ∈ Q \ S, condEntropy (fun ω => F i (X ω - Y ω))
      (fun ω => (residuePrefix K F S X ω, residuePrefix K F S Y ω)) μ) +
      subsetEntropy K μ (fun i ω => F i (Z ω)) Q -
      entropy (fun ω => X ω - Z ω) μ - entropy (fun ω => X ω - Y ω) μ -
      2 * (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
    ∑ i ∈ Q \ S, (condEntropy (fun ω => F i (X ω)) (residuePrefix K F S X) μ +
      condEntropy (fun ω => F i (Y ω)) (residuePrefix K F S Y) μ) := by
  have hp := walk_subset_remaining_prior_lower_bound μ K F Q S X Y Z
  have he := sum_subset_difference_and_prior_le_endpoints μ K F Q S X Y
  linarith

/-- Outer-batch prior with actual common-window displacement and prefix costs. -/
theorem walk_subset_window_numeric_budget (Q S : Finset ι) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N)
    (Lw : ℝ) (hN : Real.log (N + 1 : ℕ) ≤ Lw) (T : ℕ)
    (hcard : ∀ i ∈ S, Fintype.card (K i) ≤ 2 * T) :
    (∑ i ∈ Q \ S, condEntropy (fun ω => F i (z (u ω) - z (v ω)))
      (fun ω => (residuePrefix K F S (fun ω => z (u ω)) ω,
        residuePrefix K F S (fun ω => z (v ω)) ω)) μ) +
      subsetEntropy K μ (fun i ω => F i (z (t ω))) Q -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (S.card : ℝ) * Real.log (2 * T : ℕ)) ≤
    ∑ i ∈ Q \ S,
      (condEntropy (fun ω => F i (z (u ω))) (residuePrefix K F S (fun ω => z (u ω))) μ +
       condEntropy (fun ω => F i (z (v ω))) (residuePrefix K F S (fun ω => z (v ω))) μ) := by
  have h := walk_subset_retained_enrichment_budget μ K F Q S
    (fun ω => z (u ω)) (fun ω => z (v ω)) (fun ω => z (t ω))
  have hd := walk_window_displacement_entropy_cost μ z D N hstep t u v htu hu htv hv
  have hs : (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
      (S.card : ℝ) * Real.log (2 * T : ℕ) := by
    calc
      _ ≤ ∑ _i ∈ S, Real.log (2 * T : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.log_le_log (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K i)))
          (by exact_mod_cast hcard i hi)
      _ = _ := by simp
  linarith

end Points
end Source
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.entropy_subset_sub_observation_le_remaining
#print axioms BinaryFormMoat.GeometryIntegration.walk_subset_remaining_prior_lower_bound
#print axioms BinaryFormMoat.GeometryIntegration.sum_subset_difference_and_prior_le_endpoints
#print axioms BinaryFormMoat.GeometryIntegration.walk_subset_retained_enrichment_budget
#print axioms BinaryFormMoat.GeometryIntegration.walk_subset_window_numeric_budget
