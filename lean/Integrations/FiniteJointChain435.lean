import Integrations.FinitePriorChain435
import Integrations.InformationTransport435
import Mathlib.Data.Finset.Max

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Actual fresh order on a selected set: only smaller selected coordinates
are prior data. For prime subtypes this is their natural prime order. -/
def orderedCoordinatePrefix {ι : Type*} [LinearOrder ι] (S : Finset ι) (j : ι) : Finset ι :=
  S.filter (fun i => i < j)

theorem orderedCoordinatePrefix_insert_max {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (S : Finset ι) (j : ι) (hj : ∀ i ∈ S, i < j) :
    orderedCoordinatePrefix (insert j S) j = S := by
  ext i
  simp only [orderedCoordinatePrefix, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨h | h, hi⟩
    · subst i; exact (lt_irrefl _ hi).elim
    · exact h
  · intro h; exact ⟨Or.inr h, hj i h⟩

theorem orderedCoordinatePrefix_insert_old {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (S : Finset ι) (j : ι) (hj : ∀ i ∈ S, i < j) (i : ι) (hi : i ∈ S) :
    orderedCoordinatePrefix (insert j S) i = orderedCoordinatePrefix S i := by
  ext k
  simp only [orderedCoordinatePrefix, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨h | h, hk⟩
    · subst k; exact (not_lt_of_ge (hj i hi).le hk).elim
    · exact ⟨h, hk⟩
  · rintro ⟨h, hk⟩; exact ⟨Or.inr h, hk⟩

section Chain
variable {Ω ι U H : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
  [∀ i, MeasurableSingletonClass (K i)]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ∀ i, Ω → K i)
  (O : Ω → U) (W : Ω → H)

omit [LinearOrder ι] [DecidableEq ι] [∀ i, Fintype (K i)] in
theorem condEntropy_subset_empty :
    condEntropy (subsetObservation K X (∅ : Finset ι)) O μ = 0 := by
  let c : (i : (∅ : Finset ι)) → K i.val :=
    fun i => False.elim (Finset.notMem_empty i.val i.property)
  have he : subsetObservation K X (∅ : Finset ι) = fun _ : Ω => c := by
    funext ω i
    exact False.elim (Finset.notMem_empty i.val i.property)
  rw [he, condEntropy_eq_sum_fintype _ _ _ (measurable_of_finite O)]
  simp

/-- Reorder two revealed data without changing conditional entropy. -/
theorem condEntropy_condition_swap_inner {C D : Type*}
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (Y : Ω → C) (V : Ω → D) :
    condEntropy Y (fun ω => (W ω, (V ω, O ω))) μ =
      condEntropy Y (fun ω => (V ω, (W ω, O ω))) μ := by
  let f : H × (D × U) → D × (H × U) := fun v => (v.2.1, (v.1, v.2.2))
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext
    · exact congrArg (fun v : D × (H × U) => v.2.1) h
    · apply Prod.ext
      · exact congrArg (fun v : D × (H × U) => v.1) h
      · exact congrArg (fun v : D × (H × U) => v.2.2) h
  exact (condEntropy_of_injective' μ (measurable_of_finite Y)
    (measurable_of_finite (fun ω => (W ω, (V ω, O ω)))) f hf
    (measurable_of_finite _)).symm

omit [LinearOrder ι] in
/-- A fresh target coordinate exposes exactly the increment in JOINT
conditional information about the SAME original package W. -/
theorem condMutualInfo_subset_insert_sub (S : Finset ι) (j : ι) (hj : j ∉ S) :
    condMutualInfo (subsetObservation K X (insert j S)) W O μ -
      condMutualInfo (subsetObservation K X S) W O μ =
      condMutualInfo (X j) W (fun ω => (subsetObservation K X S ω, O ω)) μ := by
  have h₁ := condEntropy_subset_insert_sub K μ X O S j hj
  have h₂ := condEntropy_subset_insert_sub K μ X (fun ω => (W ω, O ω)) S j hj
  have hs := condEntropy_condition_swap_inner μ O W (X j) (subsetObservation K X S)
  rw [condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq' (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  linarith

/-- No coordinate sequence is supplied: the actual selected set's linear
order constructs the OWN prefix and the exact original-law joint telescope. -/
theorem condMutualInfo_subset_ordered_sum (S : Finset ι) :
    (∑ j ∈ S, condMutualInfo (X j) W
      (fun ω => (subsetObservation K X (orderedCoordinatePrefix S j) ω, O ω)) μ) =
      condMutualInfo (subsetObservation K X S) W O μ := by
  induction S using Finset.induction_on_max with
  | empty =>
    rw [Finset.sum_empty, condMutualInfo_eq' (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
      condEntropy_subset_empty K μ X O, condEntropy_subset_empty K μ X (fun ω => (W ω, O ω))]
    ring
  | insert j S hj ih =>
    have hnot : j ∉ S := fun h => lt_irrefl j (hj j h)
    rw [Finset.sum_insert hnot, orderedCoordinatePrefix_insert_max S j hj]
    have he : (∑ i ∈ S, condMutualInfo (X i) W
        (fun ω => (subsetObservation K X (orderedCoordinatePrefix (insert j S) i) ω, O ω)) μ) =
        ∑ i ∈ S, condMutualInfo (X i) W
        (fun ω => (subsetObservation K X (orderedCoordinatePrefix S i) ω, O ω)) μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [orderedCoordinatePrefix_insert_old S j hj i hi]
    rw [he, ih]
    have hs := condMutualInfo_subset_insert_sub K μ X O W S j hnot
    linarith

/-- The actual selected order also telescopes its conditional PRIOR entropy. -/
theorem condEntropy_subset_ordered_sum (S : Finset ι) :
    (∑ j ∈ S, condEntropy (X j)
      (fun ω => (subsetObservation K X (orderedCoordinatePrefix S j) ω, O ω)) μ) =
      condEntropy (subsetObservation K X S) O μ := by
  induction S using Finset.induction_on_max with
  | empty => simp only [Finset.sum_empty, condEntropy_subset_empty K μ X O]
  | insert j S hj ih =>
    have hnot : j ∉ S := fun h => lt_irrefl j (hj j h)
    rw [Finset.sum_insert hnot, orderedCoordinatePrefix_insert_max S j hj]
    have he : (∑ i ∈ S, condEntropy (X i)
        (fun ω => (subsetObservation K X (orderedCoordinatePrefix (insert j S) i) ω, O ω)) μ) =
        ∑ i ∈ S, condEntropy (X i)
        (fun ω => (subsetObservation K X (orderedCoordinatePrefix S i) ω, O ω)) μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [orderedCoordinatePrefix_insert_old S j hj i hi]
    rw [he, ih]
    have hs := condEntropy_subset_insert_sub K μ X O S j hnot
    linarith

end Chain

section Masks
variable {Ω ι U H C : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, AddCommGroup (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Point)
  (φ : ∀ i, Point →+ K i) (ψ : Point →+ U) (W : Ω → H)

omit [LinearOrder ι] in
/-- Fixed ambient masked data faithfully encode the actual selected prefix
for conditional INFORMATION, as well as conditional entropy. -/
theorem maskedPriorHom_condMutualInfo (X : Ω → C) (S : Finset ι) :
    condMutualInfo X W (fun ω => (maskedPriorHom K φ S (z ω), ψ (z ω))) μ =
    condMutualInfo X W (fun ω => (subsetObservation K (fun i ω => φ i (z ω)) S ω, ψ (z ω))) μ := by
  let embed : ((i : S) → K i.val) × U → ((i : ι) → K i) × U := fun v =>
    ((fun i => if h : i ∈ S then v.1 ⟨i, h⟩ else 0), v.2)
  have he : Function.Injective embed := by
    intro v w h
    apply Prod.ext
    · funext i
      have hi := congrFun (congrArg Prod.fst h) i.val
      simpa [embed, i.property] using hi
    · exact congrArg (fun v : ((i : ι) → K i) × U => v.2) h
  let Y := fun ω => (subsetObservation K (fun i ω => φ i (z ω)) S ω, ψ (z ω))
  have hfaith : embed ∘ Y = (fun ω => (maskedPriorHom K φ S (z ω), ψ (z ω))) := by
    funext ω
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ S <;> simp [embed, Y, maskedPriorHom, subsetObservation, hi]
    · rfl
  rw [← hfaith]
  exact condMutualInfo_of_inj (measurable_of_finite X) (measurable_of_finite W)
    (measurable_of_finite Y) μ he

omit [LinearOrder ι] in
/-- Target masking also preserves joint package information exactly. -/
theorem maskedPriorHom_target_condMutualInfo (S : Finset ι) :
    condMutualInfo (fun ω => maskedPriorHom K φ S (z ω)) W (fun ω => ψ (z ω)) μ =
      condMutualInfo (subsetObservation K (fun i ω => φ i (z ω)) S) W (fun ω => ψ (z ω)) μ := by
  let embed : ((i : S) → K i.val) → ((i : ι) → K i) :=
    fun v i => if h : i ∈ S then v ⟨i, h⟩ else 0
  have he : Function.Injective embed := by
    intro v w h
    funext i
    have hi := congrFun h i.val
    simpa [embed, i.property] using hi
  have hfaith : embed ∘ subsetObservation K (fun i ω => φ i (z ω)) S =
      (fun ω => maskedPriorHom K φ S (z ω)) := by
    funext ω i
    by_cases hi : i ∈ S <;> simp [embed, maskedPriorHom, subsetObservation, hi]
  rw [← hfaith]
  exact condMutualInfo_of_inj_map (measurable_of_finite _) (measurable_of_finite W)
    (measurable_of_finite _) (fun _ => embed) (fun _ => he)

/-- ACTUAL ordered additive prefixes aggregate into one JOINT package
information on the SAME original source, ready for one displacement charge. -/
theorem maskedPriorHom_ordered_information_sum (S : Finset ι) :
    (∑ j ∈ S, condMutualInfo (fun ω => φ j (z ω)) W
      (fun ω => (maskedPriorHom K φ (orderedCoordinatePrefix S j) (z ω), ψ (z ω))) μ) =
      condMutualInfo (fun ω => maskedPriorHom K φ S (z ω)) W (fun ω => ψ (z ω)) μ := by
  simp_rw [maskedPriorHom_condMutualInfo K μ z φ ψ W]
  rw [maskedPriorHom_target_condMutualInfo K μ z φ ψ W]
  exact condMutualInfo_subset_ordered_sum K μ (fun i ω => φ i (z ω)) (fun ω => ψ (z ω)) W S

/-- Actual masked prefixes preserve the summed original joint prior entropy. -/
theorem maskedPriorHom_ordered_entropy_sum (S : Finset ι) :
    (∑ j ∈ S, condEntropy (fun ω => φ j (z ω))
      (fun ω => (maskedPriorHom K φ (orderedCoordinatePrefix S j) (z ω), ψ (z ω))) μ) =
      condEntropy (fun ω => maskedPriorHom K φ S (z ω)) (fun ω => ψ (z ω)) μ := by
  have he : (∑ j ∈ S, condEntropy (fun ω => φ j (z ω))
      (fun ω => (maskedPriorHom K φ (orderedCoordinatePrefix S j) (z ω), ψ (z ω))) μ) =
      ∑ j ∈ S, condEntropy (fun ω => φ j (z ω))
      (fun ω => (subsetObservation K (fun i ω => φ i (z ω)) (orderedCoordinatePrefix S j) ω, ψ (z ω))) μ := by
    apply Finset.sum_congr rfl
    intro j _
    exact maskedPriorHom_condEntropy K μ z (fun ω => φ j (z ω)) φ ψ _
  rw [he, maskedPriorHom_target_condEntropy K μ z φ ψ]
  exact condEntropy_subset_ordered_sum K μ (fun i ω => φ i (z ω)) (fun ω => ψ (z ω)) S

end Masks
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.orderedCoordinatePrefix
#print axioms BinaryFormMoat.EntropyIntegration.orderedCoordinatePrefix_insert_max
#print axioms BinaryFormMoat.EntropyIntegration.orderedCoordinatePrefix_insert_old
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_subset_empty
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_condition_swap_inner
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_subset_insert_sub
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_subset_ordered_sum
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_condMutualInfo
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_target_condMutualInfo
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_ordered_information_sum

#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_subset_ordered_sum
#print axioms BinaryFormMoat.EntropyIntegration.maskedPriorHom_ordered_entropy_sum
