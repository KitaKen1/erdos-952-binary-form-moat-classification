import Integrations.FairDifferenceEntropy435
import Integrations.CoordinateEntropy435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The PFR API has a finite-codomain instance; physical observations instead
use the actual finite source, so their codomain may remain the whole Z^2. -/
instance finiteSource_finiteRange {Ω G : Type*} [Finite Ω] (X : Ω → G) : FiniteRange X where
  finite := Set.finite_range X

section FiniteSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem condEntropy_pair_le_add_finite {S T O : Type*}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → O) :
    condEntropy (fun ω => (X ω, Y ω)) Z μ ≤ condEntropy X Z μ + condEntropy Y Z μ := by
  have hc := cond_chain_rule' μ (measurable_of_finite X) (measurable_of_finite Y)
    (measurable_of_finite Z)
  have hs := entropy_submodular μ (measurable_of_finite Y) (measurable_of_finite X)
    (measurable_of_finite Z)
  linarith

/-- Keep the entropy left in X after the ENTIRE physical difference is known.
No independence of endpoint, prefix or displacement variables is used. -/
theorem condEntropy_difference_retains_full_data {Q D A B : Type*}
    [AddCommGroup Q] [Countable Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Countable D] [MeasurableSpace D] [MeasurableSingletonClass D]
    [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (X Y : Ω → Q) (h : Ω → D) (φ : D → Q) (Bx : Ω → A) (By : Ω → B)
    (hdiff : ∀ ω, X ω - Y ω = φ (h ω)) :
    condEntropy (fun ω => X ω - Y ω) (fun ω => (Bx ω, By ω)) μ +
      condEntropy X (fun ω => (h ω, (Bx ω, By ω))) μ ≤
        condEntropy X Bx μ + condEntropy Y By μ := by
  let Z := fun ω => (Bx ω, By ω)
  let shear : Q × Q → Q × Q := fun v => (v.1 - v.2, v.1)
  have hi : Function.Injective shear := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ he
    have hx : x = x' := congrArg Prod.snd he
    subst x'
    have hy : x - y = x - y' := congrArg Prod.fst he
    exact Prod.ext rfl (sub_right_inj.mp hy)
  have he := condEntropy_comp_of_injective (Y := Z) μ
    (measurable_of_finite (fun ω => (X ω, Y ω))) shear hi
  simp only [Function.comp_def, shear] at he
  have hc := cond_chain_rule' μ (measurable_of_finite (fun ω => X ω - Y ω))
    (measurable_of_finite X) (measurable_of_finite Z)
  have hh := condEntropy_comp_ge μ (measurable_of_finite (fun ω => (h ω, Z ω)))
    (measurable_of_finite X) (fun v : D × (A × B) => (φ v.1, v.2))
  simp only [Function.comp_def, ← hdiff] at hh
  have hp := condEntropy_pair_le_add_finite μ X Y Z
  have hx := condEntropy_comp_ge μ (measurable_of_finite Z)
    (measurable_of_finite X) Prod.fst
  have hy := condEntropy_comp_ge μ (measurable_of_finite Z)
    (measurable_of_finite Y) Prod.snd
  change condEntropy X Z μ ≤ condEntropy X Bx μ at hx
  change condEntropy Y Z μ ≤ condEntropy Y By μ at hy
  change _ + condEntropy X (fun ω => (h ω, Z ω)) μ ≤ _
  linarith

theorem entropy_projection_prior_ge_sub_displacement {Q : Type*}
    [AddCommGroup Q] [Countable Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (F : Point →+ Q) (X Z : Ω → Point) :
    entropy (fun ω => F (Z ω)) μ - entropy (fun ω => X ω - Z ω) μ ≤
      entropy (fun ω => F (X ω)) μ := by
  let W := fun ω => (F (X ω), X ω - Z ω)
  let g : Q × Point → Q := fun v => v.1 - F v.2
  have he : g ∘ W = (fun ω => F (Z ω)) := by
    funext ω
    simp only [g, W, Function.comp_def, map_sub, sub_sub_cancel]
  have hl := entropy_comp_le μ (measurable_of_finite W) g
  rw [he] at hl
  have hp := entropy_pair_le_add (measurable_of_finite (fun ω => F (X ω)))
    (measurable_of_finite (fun ω => X ω - Z ω)) μ
  change entropy W μ ≤ _ at hp
  linarith

theorem condEntropy_of_function_eq_zero_finite {S O : Type*}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (Z : Ω → O) (f : O → S) : condEntropy (f ∘ Z) Z μ = 0 := by
  rw [chain_rule'' μ (measurable_of_finite _) (measurable_of_finite Z),
    entropy_comm (measurable_of_finite _) (measurable_of_finite Z),
    entropy_prod_comp (measurable_of_finite Z) μ f, sub_self]

theorem entropy_sub_observation_le_condEntropy_finite {S O : Type*}
    [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (X : Ω → S) (Z : Ω → O) : entropy X μ - entropy Z μ ≤ condEntropy X Z μ := by
  rw [chain_rule'' μ (measurable_of_finite X) (measurable_of_finite Z),
    chain_rule' μ (measurable_of_finite X) (measurable_of_finite Z)]
  have hn := condEntropy_nonneg Z X μ
  linarith

/-- Extend the selected PFR finite-coordinate API to a countable physical
observation; finite source support ensures finite range even when O=Z^2. -/
theorem condEntropy_pi_le_sum_countable_observation {ι O : Type*}
    [Fintype ι] [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (X : ∀ i, Ω → K i) (Z : Ω → O) :
    condEntropy (fun ω i => X i ω) Z μ ≤ ∑ i, condEntropy (X i) Z μ := by
  classical
  simp_rw [condEntropy_eq_sum _ _ _ (measurable_of_finite Z)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (entropy_pi_le_sum (μ[|Z ← z]) K X (fun i => measurable_of_finite (X i)))
    measureReal_nonneg

/-- Known prefix coordinates contribute zero conditional entropy; the
remaining-coordinate sum retains the FULL joint prior minus one data cost. -/
theorem entropy_pi_sub_observation_le_remaining {ι O : Type*}
    [Fintype ι] [DecidableEq ι] [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (X : ∀ i, Ω → K i) (Z : Ω → O)
    (S : Finset ι) (hknown : ∀ i ∈ S, ∃ f : O → K i, ∀ ω, X i ω = f (Z ω)) :
    entropy (fun ω i => X i ω) μ - entropy Z μ ≤
      ∑ i ∈ Finset.univ \ S, condEntropy (X i) Z μ := by
  classical
  have hz (i : ι) (hi : i ∈ S) : condEntropy (X i) Z μ = 0 := by
    obtain ⟨f, hf⟩ := hknown i hi
    have he : X i = f ∘ Z := funext hf
    rw [he]
    exact condEntropy_of_function_eq_zero_finite μ Z f
  have hs : (∑ i ∈ Finset.univ \ S, condEntropy (X i) Z μ) =
      ∑ i, condEntropy (X i) Z μ := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro i _ hi
    apply hz
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hi
  rw [hs]
  exact (entropy_sub_observation_le_condEntropy_finite μ _ Z).trans
    (condEntropy_pi_le_sum_countable_observation μ K X Z)

end FiniteSource
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.finiteSource_finiteRange
#print axioms BinaryFormMoat.GeometryIntegration.condEntropy_pair_le_add_finite
#print axioms BinaryFormMoat.GeometryIntegration.condEntropy_difference_retains_full_data
#print axioms BinaryFormMoat.GeometryIntegration.entropy_projection_prior_ge_sub_displacement
#print axioms BinaryFormMoat.GeometryIntegration.condEntropy_of_function_eq_zero_finite
#print axioms BinaryFormMoat.GeometryIntegration.entropy_sub_observation_le_condEntropy_finite
#print axioms BinaryFormMoat.GeometryIntegration.condEntropy_pi_le_sum_countable_observation
#print axioms BinaryFormMoat.GeometryIntegration.entropy_pi_sub_observation_le_remaining
