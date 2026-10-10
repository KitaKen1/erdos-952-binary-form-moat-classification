import Integrations.SubsetEntropy435
import Integrations.RootResidues435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Selected additive residues embedded in one fixed finite ambient alphabet.
The selected set may vary with the target and auxiliary root assignment. -/
def maskedPriorHom {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (φ : ∀ i, Point →+ K i) (A : Finset ι) :
    Point →+ ((i : ι) → K i) where
  toFun z i := if i ∈ A then φ i z else 0
  map_zero' := by funext i; simp
  map_add' := by intro z w; funext i; by_cases hi : i ∈ A <;> simp [hi]

theorem maskedPriorHom_selected {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (φ : ∀ i, Point →+ K i) (A : Finset ι)
    (z : Point) (i : A) : maskedPriorHom K φ A z i.val = φ i.val z := by
  simp [maskedPriorHom, i.property]

/-- Exact conditional insert chain rule with an existing prior observation.
The revealed subset is the actual prefix, not a larger full-data tuple. -/
theorem condEntropy_subset_insert_sub {Ω ι U : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ∀ i, Ω → K i) (O : Ω → U)
    (A : Finset ι) (j : ι) (_hj : j ∉ A) :
    condEntropy (subsetObservation K X (insert j A)) O μ -
      condEntropy (subsetObservation K X A) O μ =
      condEntropy (X j) (fun ω => (subsetObservation K X A ω, O ω)) μ := by
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
  have hp := condEntropy_comp_of_injective (Y := O) μ
    (measurable_of_finite (subsetObservation K X (insert j A))) extract hi
  have he : extract ∘ subsetObservation K X (insert j A) =
      (fun ω => (X j ω, subsetObservation K X A ω)) := rfl
  rw [he] at hp
  rw [← hp, cond_chain_rule μ (measurable_of_finite (X j))
    (measurable_of_finite (subsetObservation K X A)) (measurable_of_finite O)]
  ring

/-- The additive masked prior used by root packages faithfully records
precisely the selected prefix plus the existing smaller-batch prior. -/
theorem maskedPriorHom_condEntropy {Ω ι U C : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, AddCommGroup (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Point) (X : Ω → C)
    (φ : ∀ i, Point →+ K i) (ψ : Point →+ U) (A : Finset ι) :
    condEntropy X (fun ω => (maskedPriorHom K φ A (z ω), ψ (z ω))) μ =
    condEntropy X (fun ω => (subsetObservation K (fun i ω => φ i (z ω)) A ω, ψ (z ω))) μ := by
  let embed : ((i : A) → K i.val) × U → ((i : ι) → K i) × U := fun v =>
    ((fun i => if h : i ∈ A then v.1 ⟨i, h⟩ else 0), v.2)
  have he : Function.Injective embed := by
    intro v w h
    apply Prod.ext
    · funext i
      have hi := congrFun (congrArg Prod.fst h) i.val
      simpa [embed, i.property] using hi
    · simpa only [embed] using
        congrArg (fun v : ((i : ι) → K i) × U => v.2) h
  let Y := fun ω => (subsetObservation K (fun i ω => φ i (z ω)) A ω, ψ (z ω))
  have hfaith : embed ∘ Y = (fun ω => (maskedPriorHom K φ A (z ω), ψ (z ω))) := by
    funext ω
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ A <;> simp [embed, Y, maskedPriorHom, subsetObservation, hi]
    · rfl
  rw [← hfaith]
  exact condEntropy_of_injective' μ (measurable_of_finite X)
    (measurable_of_finite Y) embed he (measurable_of_finite _)

section AdditiveChain
variable {Ω ι U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι] [DecidableEq ι] (K : ι → Type*)
  [∀ i, Fintype (K i)] [∀ i, AddCommGroup (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Point)
  (φ : ∀ i, Point →+ K i) (ψ : Point →+ U)

omit [Fintype U] [MeasurableSingletonClass U] [IsProbabilityMeasure μ] in
/-- Embedding selected residues in the fixed ambient alphabet preserves
their conditional entropy as a TARGET, as well as their role as prior data. -/
theorem maskedPriorHom_target_condEntropy (A : Finset ι) :
    condEntropy (fun ω => maskedPriorHom K φ A (z ω)) (fun ω => ψ (z ω)) μ =
    condEntropy (subsetObservation K (fun i ω => φ i (z ω)) A) (fun ω => ψ (z ω)) μ := by
  let embed : ((i : A) → K i.val) → ((i : ι) → K i) :=
    fun v i => if h : i ∈ A then v ⟨i, h⟩ else 0
  have he : Function.Injective embed := by
    intro v w h
    funext i
    have hi := congrFun h i.val
    simpa [embed, i.property] using hi
  have hfaith : embed ∘ subsetObservation K (fun i ω => φ i (z ω)) A =
      (fun ω => maskedPriorHom K φ A (z ω)) := by
    funext ω i
    by_cases hi : i ∈ A <;> simp [embed, maskedPriorHom, subsetObservation, hi]
  rw [← hfaith]
  exact condEntropy_comp_of_injective μ (measurable_of_finite _) embed he

/-- A fresh coordinate's actual additive prior consists of the selected
prefix and existing smaller-batch residues. This is an exact chain increment. -/
theorem maskedPriorHom_chain_step (A : Finset ι) (j : ι) (hj : j ∉ A) :
    condEntropy (fun ω => maskedPriorHom K φ (insert j A) (z ω)) (fun ω => ψ (z ω)) μ -
      condEntropy (fun ω => maskedPriorHom K φ A (z ω)) (fun ω => ψ (z ω)) μ =
      condEntropy (fun ω => φ j (z ω))
        (fun ω => (maskedPriorHom K φ A (z ω), ψ (z ω))) μ := by
  rw [maskedPriorHom_target_condEntropy K μ z φ ψ (insert j A),
    maskedPriorHom_target_condEntropy K μ z φ ψ A,
    condEntropy_subset_insert_sub K μ (fun i ω => φ i (z ω)) (fun ω => ψ (z ω)) A j hj]
  exact (maskedPriorHom_condEntropy K μ z (fun ω => φ j (z ω)) φ ψ A).symm

/-- Exact finite telescope for an arbitrary supplied fresh-coordinate order.
Every term uses its OWN actual prefix prior; the original source law and the
existing smaller-batch prior are retained throughout. -/
theorem maskedPriorHom_chain_sum (A : ℕ → Finset ι) (j : ℕ → ι) (n : ℕ)
    (hinsert : ∀ k < n, A (k + 1) = insert (j k) (A k))
    (hfresh : ∀ k < n, j k ∉ A k) :
    (∑ k ∈ Finset.range n, condEntropy (fun ω => φ (j k) (z ω))
      (fun ω => (maskedPriorHom K φ (A k) (z ω), ψ (z ω))) μ) =
    condEntropy (fun ω => maskedPriorHom K φ (A n) (z ω)) (fun ω => ψ (z ω)) μ -
      condEntropy (fun ω => maskedPriorHom K φ (A 0) (z ω)) (fun ω => ψ (z ω)) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,
      ih (fun k hk => hinsert k (by omega)) (fun k hk => hfresh k (by omega)),
      ← maskedPriorHom_chain_step K μ z φ ψ (A n) (j n) (hfresh n (by omega)),
      ← hinsert n (by omega)]
    ring

end AdditiveChain
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_selected
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_subset_insert_sub
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_condEntropy
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_target_condEntropy
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_chain_step
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_chain_sum
