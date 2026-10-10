import Integrations.SubsetIncrement435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Coordinates
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
  [∀ i, MeasurableSingletonClass (K i)]
  (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
  (X : ∀ i, Ω → K i) (hX : ∀ i, Measurable (X i))

/-- Dependent coordinate tuple restricted to a fixed subset. -/
def subsetObservation (A : Finset ι) : Ω → ((i : A) → K i.val) := fun ω i => X i.val ω

def subsetEntropy (A : Finset ι) : ℝ := entropy (subsetObservation K X A) μ

omit [IsZeroOrProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (K i)] [∀ i, MeasurableSingletonClass (K i)] in
include hX in
theorem measurable_subsetObservation (A : Finset ι) :
    Measurable (subsetObservation K X A) := Measurable.of_eval (fun i => hX i.val)

omit [DecidableEq ι] [∀ i, Fintype (K i)] in
theorem subsetEntropy_empty : subsetEntropy K μ X ∅ = 0 := by
  have : Subsingleton ((i : ↥(∅ : Finset ι)) → K i.val) := by
    refine ⟨fun v w => ?_⟩
    funext i
    exact False.elim (Finset.notMem_empty i.val i.property)
  let c : (i : ↥(∅ : Finset ι)) → K i.val := fun i => False.elim (Finset.notMem_empty i.val i.property)
  have he : subsetObservation K X ∅ = (fun _ : Ω => c) := by
    funext ω
    exact Subsingleton.elim _ _
  rw [subsetEntropy, he]
  exact entropy_const _

include hX in
/-- Adding a fresh coordinate is exactly its conditional entropy. -/
theorem subsetEntropy_insert_sub (A : Finset ι) (j : ι) (_hj : j ∉ A) :
    subsetEntropy K μ X (insert j A) - subsetEntropy K μ X A =
      condEntropy (X j) (subsetObservation K X A) μ := by
  classical
  let extract : ((i : ↥(insert j A : Finset ι)) → K i.val) → K j × ((i : A) → K i.val) :=
    fun v => (v ⟨j, Finset.mem_insert_self _ _⟩,
      fun i => v ⟨i.val, Finset.mem_insert_of_mem i.property⟩)
  have hi : Function.Injective extract := by
    intro v w he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    funext i
    rcases Finset.mem_insert.mp i.property with hji | hA
    · have ei : i = ⟨j, Finset.mem_insert_self j A⟩ := Subtype.ext hji
      subst i
      exact he1
    · exact congrFun he2 ⟨i.val, hA⟩
  have hp := entropy_comp_of_injective μ (measurable_subsetObservation K X hX (insert j A)) extract hi
  have he : extract ∘ subsetObservation K X (insert j A) =
      (fun ω => (X j ω, subsetObservation K X A ω)) := rfl
  rw [he] at hp
  rw [chain_rule'' μ (hX j) (measurable_subsetObservation K X hX A), hp]
  rfl

include hX in
/-- More revealed coordinates decrease the entropy of a fresh coordinate. -/
theorem subsetEntropy_diminishing_returns (A B : Finset ι) (hAB : A ⊆ B)
    (j : ι) (hj : j ∉ B) :
    subsetEntropy K μ X (insert j B) - subsetEntropy K μ X B ≤
      subsetEntropy K μ X (insert j A) - subsetEntropy K μ X A := by
  have hjA : j ∉ A := fun ha => hj (hAB ha)
  rw [subsetEntropy_insert_sub K μ X hX B j hj,
    subsetEntropy_insert_sub K μ X hX A j hjA]
  let restrict : ((i : B) → K i.val) → ((i : A) → K i.val) :=
    fun v i => v ⟨i.val, hAB i.property⟩
  exact condEntropy_comp_ge μ (measurable_subsetObservation K X hX B) (hX j) restrict

include hX in
/-- Han's bound uses the actual entropies of fixed coordinate subsets. -/
theorem subsetEntropy_sum_erase_le (B : Finset ι) :
    (∑ j ∈ B, (subsetEntropy K μ X B - subsetEntropy K μ X (B.erase j))) ≤
      subsetEntropy K μ X B := by
  simpa only [subsetEntropy_empty K μ X, sub_zero] using
    sum_erase_marginals_le (subsetEntropy K μ X)
      (subsetEntropy_diminishing_returns K μ X hX) B

include hX in
/-- Exact mean conditional entropy for one fresh uniformly chosen coordinate. -/
theorem subsetEntropy_average_fresh (s : ℕ) (hs : s < Fintype.card ι) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
      ∑ j ∈ Finset.univ \ A, condEntropy (X j) (subsetObservation K X A) μ) /
      (((Finset.univ : Finset ι).powersetCard s).card * (Fintype.card ι - s) : ℕ) =
    subsetMean (s + 1) (subsetEntropy K μ X) - subsetMean s (subsetEntropy K μ X) := by
  have he : (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
      ∑ j ∈ Finset.univ \ A, condEntropy (X j) (subsetObservation K X A) μ) =
      ∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
        ∑ j ∈ Finset.univ \ A,
          (subsetEntropy K μ X (insert j A) - subsetEntropy K μ X A) := by
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro j hj
    exact (subsetEntropy_insert_sub K μ X hX A j (Finset.mem_sdiff.mp hj).2).symm
  rw [he]
  exact subsetMean_increment s hs _

include hX in
/-- The forward-difference estimate required for normalized enrichment. -/
theorem subsetEntropy_forward_increment_le (s : ℕ) (hs : 0 < s)
    (hsk : s < Fintype.card ι) :
    subsetMean (s + 1) (subsetEntropy K μ X) - subsetMean s (subsetEntropy K μ X) ≤
      subsetMean s (subsetEntropy K μ X) / s :=
  subsetMean_forward_increment_le s hs hsk _ (subsetEntropy_empty K μ X)
    (subsetEntropy_diminishing_returns K μ X hX)

end Coordinates
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.subsetObservation
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy
#print axioms BinaryFormMoat.EntropyIntegration.measurable_subsetObservation
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_empty
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_insert_sub
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_diminishing_returns
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_sum_erase_le
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_average_fresh
#print axioms BinaryFormMoat.EntropyIntegration.subsetEntropy_forward_increment_le
