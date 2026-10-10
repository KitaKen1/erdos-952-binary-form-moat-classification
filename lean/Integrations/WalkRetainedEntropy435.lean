import Integrations.RetainedDifferenceEntropy435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Residues
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι] [DecidableEq ι] (K : ι → Type*)
  [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ∀ i, Point →+ K i)

def fullPointProjection : Point →+ (∀ i, K i) where
  toFun x i := F i x
  map_zero' := by ext i; exact map_zero _
  map_add' x y := by ext i; exact map_add _ _ _

def residuePrefix (S : Finset ι) (X : Ω → Point) : Ω → ((i : S) → K i.val) :=
  fun ω i => F i.val (X ω)

def residueDifferenceObservation (S : Finset ι) (X Y : Ω → Point) :
    Ω → Point × (((i : S) → K i.val) × ((i : S) → K i.val)) :=
  fun ω => (X ω - Y ω, (residuePrefix K F S X ω, residuePrefix K F S Y ω))

omit [Fintype Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ] in
theorem residuePrefix_entropy_le_log_card_sum (S : Finset ι) (X : Ω → Point) :
    entropy (residuePrefix K F S X) μ ≤ ∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ) := by
  classical
  have h := entropy_le_log_card (residuePrefix K F S X) μ
  rw [Fintype.card_pi, Nat.cast_prod,
    Real.log_prod (fun i _ => by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (K i.val) ≠ 0))]
    at h
  exact h.trans_eq (Finset.sum_coe_sort S (fun i => Real.log (Fintype.card (K i) : ℝ)))

/-- Starting entropy is retained on the ORIGINAL common point law. The
prefix cost is derived from its actual finite alphabets, not assumed small. -/
theorem walk_remaining_residue_prior_lower_bound (S : Finset ι) (X Y Z : Ω → Point) :
    entropy (fun ω i => F i (Z ω)) μ - entropy (fun ω => X ω - Z ω) μ -
      entropy (fun ω => X ω - Y ω) μ -
      2 * (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
        ∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (X ω))
          (residueDifferenceObservation K F S X Y) μ := by
  classical
  let Bx := residuePrefix K F S X
  let By := residuePrefix K F S Y
  let O := residueDifferenceObservation K F S X Y
  have hr := entropy_pi_sub_observation_le_remaining μ K (fun i ω => F i (X ω)) O S (by
    intro i hi
    exact ⟨(fun o => o.2.1 ⟨i, hi⟩), fun _ => rfl⟩)
  have hp := entropy_projection_prior_ge_sub_displacement μ (fullPointProjection K F) X Z
  change entropy (fun ω i => F i (Z ω)) μ - entropy (fun ω => X ω - Z ω) μ ≤
    entropy (fun ω i => F i (X ω)) μ at hp
  have ho := entropy_pair_le_add (measurable_of_finite (fun ω => X ω - Y ω))
    (measurable_of_finite (fun ω => (Bx ω, By ω))) μ
  change entropy O μ ≤ _ at ho
  have hb := entropy_pair_le_add (measurable_of_finite Bx) (measurable_of_finite By) μ
  have hx := residuePrefix_entropy_le_log_card_sum K μ F S X
  have hy := residuePrefix_entropy_le_log_card_sum K μ F S Y
  change entropy Bx μ ≤ _ at hx
  change entropy By μ ≤ _ at hy
  linarith

theorem sum_residue_difference_and_prior_le_endpoints (S : Finset ι) (X Y : Ω → Point) :
    (∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (X ω - Y ω))
      (fun ω => (residuePrefix K F S X ω, residuePrefix K F S Y ω)) μ) +
    (∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (X ω))
      (residueDifferenceObservation K F S X Y) μ) ≤
    ∑ i ∈ Finset.univ \ S, (condEntropy (fun ω => F i (X ω)) (residuePrefix K F S X) μ +
      condEntropy (fun ω => F i (Y ω)) (residuePrefix K F S Y) μ) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := condEntropy_difference_retains_full_data μ
    (fun ω => F i (X ω)) (fun ω => F i (Y ω)) (fun ω => X ω - Y ω) (F i)
    (residuePrefix K F S X) (residuePrefix K F S Y) (fun ω => (map_sub (F i) _ _).symm)
  change _ + condEntropy (fun ω => F i (X ω))
    (residueDifferenceObservation K F S X Y) μ ≤ _ at h
  simpa only [map_sub] using h

/-- Finite enrichment budget: supply the geometric difference-coordinate
floor kappa, and the ORIGINAL starting joint entropy survives explicitly. -/
theorem walk_residue_retained_enrichment_budget (S : Finset ι) (X Y Z : Ω → Point) (κ : ℝ)
    (hκ : κ ≤ ∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (X ω - Y ω))
      (fun ω => (residuePrefix K F S X ω, residuePrefix K F S Y ω)) μ) :
    κ + entropy (fun ω i => F i (Z ω)) μ - entropy (fun ω => X ω - Z ω) μ -
      entropy (fun ω => X ω - Y ω) μ -
      2 * (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
    ∑ i ∈ Finset.univ \ S, (condEntropy (fun ω => F i (X ω)) (residuePrefix K F S X) μ +
      condEntropy (fun ω => F i (Y ω)) (residuePrefix K F S Y) μ) := by
  have hr := walk_remaining_residue_prior_lower_bound K μ F S X Y Z
  have hc := sum_residue_difference_and_prior_le_endpoints K μ F S X Y
  linarith

end Residues
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.residuePrefix_entropy_le_log_card_sum
#print axioms BinaryFormMoat.GeometryIntegration.walk_remaining_residue_prior_lower_bound
#print axioms BinaryFormMoat.GeometryIntegration.sum_residue_difference_and_prior_le_endpoints
#print axioms BinaryFormMoat.GeometryIntegration.walk_residue_retained_enrichment_budget
