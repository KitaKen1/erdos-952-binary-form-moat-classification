import Integrations.FiniteProductAverage435
import Integrations.FamilyResiduePrior435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration

/-- One genuine fixed-size subset and global root-label choice. -/
abbrev LabelledBatchChoice (P : Finset ℕ) (Q : Type*) [Fintype Q] (s : ℕ) :=
  ↥(labelledSubsetChoices (ι := P) (R := Q) s)

theorem labelledBatchChoice_nonempty (P : Finset ℕ) (Q : Type*) [Fintype Q] [Nonempty Q]
    (s : ℕ) (hs : s ≤ P.card) : Nonempty (LabelledBatchChoice P Q s) :=
  (labelledSubsetChoices_nonempty s (by simpa only [Fintype.card_coe] using hs)).coe_sort

theorem labelledBatchChoice_mean (P : Finset ℕ) (Q : Type*) [Fintype Q] (s : ℕ)
    (f : Finset P → (P → Q) → ℝ) :
    finiteUniformMean (fun q : LabelledBatchChoice P Q s => f q.val.1 q.val.2) =
      subsetLabelAverage s f := by
  rw [subsetLabelAverage_eq_choicesMean]
  simp only [finiteUniformMean, Fintype.card_coe]
  rw [Finset.sum_coe_sort (labelledSubsetChoices (ι := P) (R := Q) s)
    (fun q => f q.1 q.2)]

end BinaryFormMoat.EntropyIntegration
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The actual finite dependent PRODUCT of all selected batch choices. -/
abbrev FamilyAuxiliaryChoice (I : Finset ℕ) (P : ℕ → Finset ℕ) (Q : Type*) [Fintype Q]
    (s : I → ℕ) := (i : I) → LabelledBatchChoice (P i.val) Q (s i)

def familyAuxiliaryHom (I : Finset ℕ) (P : ℕ → Finset ℕ) (Q : Type*) [Fintype Q]
    (s : I → ℕ) (F : ∀ i : I, ∀ p : P i.val, Q → Point →+ ZMod p.val)
    (a : FamilyAuxiliaryChoice I P Q s) (i : I) : Point →+ ((p : P i.val) → ZMod p.val) :=
  maskedPriorHom (fun p : P i.val => ZMod p.val) (fun p => F i p ((a i).val.2 p)) (a i).val.1

/-- Replacing the CURRENT choice changes exactly its actual selected tuple. -/
theorem familyAuxiliaryHom_update_self (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Q : Type*) [Fintype Q] (s : I → ℕ)
    (F : ∀ i : I, ∀ p : P i.val, Q → Point →+ ZMod p.val)
    (a : FamilyAuxiliaryChoice I P Q s) (j : I) (q : LabelledBatchChoice (P j.val) Q (s j)) :
    familyAuxiliaryHom I P Q s F (Function.update a j q) j =
      maskedPriorHom (fun p : P j.val => ZMod p.val) (fun p => F j p (q.val.2 p)) q.val.1 := by
  simp only [familyAuxiliaryHom, Function.update_self]

/-- The ACTUAL earlier selected prior is unchanged by refreshing the current
coordinate. No larger alphabet replaces it in the conditioning experiment. -/
theorem familyEarlierAuxiliaryHom_update (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Q : Type*) [Fintype Q] (s : I → ℕ)
    (F : ∀ i : I, ∀ p : P i.val, Q → Point →+ ZMod p.val)
    (a : FamilyAuxiliaryChoice I P Q s) (j : I) (q : LabelledBatchChoice (P j.val) Q (s j)) :
    familyEarlierHom I P (familyAuxiliaryHom I P Q s F (Function.update a j q)) j.val =
      familyEarlierHom I P (familyAuxiliaryHom I P Q s F a) j.val := by
  ext x i p
  by_cases hi : i < j
  · have hne : i ≠ j := by intro he; subst i; exact (lt_irrefl _ hi)
    simp [familyEarlierHom, maskedPriorHom, hi, familyAuxiliaryHom, hne]
  · simp [familyEarlierHom, maskedPriorHom, hi]

/-- Refresh averaging is exactly the original subset/root average, with
the original earlier prior held fixed and the original law unchanged. -/
theorem familyAuxiliary_information_refresh (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Q : Type*) [Fintype Q] (s : I → ℕ) [∀ i : I, ∀ p : P i.val, NeZero p.val]
    (F : ∀ i : I, ∀ p : P i.val, Q → Point →+ ZMod p.val)
    (a : FamilyAuxiliaryChoice I P Q s) (j : I) (μ : Measure ℕ)
    (z : ℕ → Point) {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (W : ℕ → T) (L : ℝ) :
    finiteUniformMean (fun q : LabelledBatchChoice (P j.val) Q (s j) =>
      condMutualInfo (fun v => familyAuxiliaryHom I P Q s F (Function.update a j q) j (z v)) W
        (fun v => familyEarlierHom I P (familyAuxiliaryHom I P Q s F (Function.update a j q)) j.val (z v)) μ / L) =
      subsetLabelAverage (s j) (fun C label =>
        condMutualInfo (fun v => maskedPriorHom (fun p : P j.val => ZMod p.val)
          (fun p => F j p (label p)) C (z v)) W
          (fun v => familyEarlierHom I P (familyAuxiliaryHom I P Q s F a) j.val (z v)) μ / L) := by
  simp_rw [familyAuxiliaryHom_update_self, familyEarlierAuxiliaryHom_update]
  exact labelledBatchChoice_mean (P j.val) Q (s j) (fun C label =>
    condMutualInfo (fun v => maskedPriorHom (fun p : P j.val => ZMod p.val)
      (fun p => F j p (label p)) C (z v)) W
      (fun v => familyEarlierHom I P (familyAuxiliaryHom I P Q s F a) j.val (z v)) μ / L)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.EntropyIntegration.LabelledBatchChoice
#print axioms BinaryFormMoat.EntropyIntegration.labelledBatchChoice_nonempty
#print axioms BinaryFormMoat.EntropyIntegration.labelledBatchChoice_mean
#print axioms BinaryFormMoat.GeometryIntegration.FamilyAuxiliaryChoice
#print axioms BinaryFormMoat.GeometryIntegration.familyAuxiliaryHom
#print axioms BinaryFormMoat.GeometryIntegration.familyAuxiliaryHom_update_self
#print axioms BinaryFormMoat.GeometryIntegration.familyEarlierAuxiliaryHom_update
#print axioms BinaryFormMoat.GeometryIntegration.familyAuxiliary_information_refresh
