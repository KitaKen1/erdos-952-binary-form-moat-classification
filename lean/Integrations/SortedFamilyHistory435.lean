import Integrations.FiniteFamilyHistory435
import Integrations.FamilyResiduePrior435
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Canonical increasing order of the ACTUAL selected batch indices. -/
def selectedFamilyOrder (I : Finset ℕ) : Fin I.card ≃o I := I.orderIsoOfFin rfl

theorem selectedFamilyOrder_prefix (I : Finset ℕ) (j : I) (k : Fin I.card) :
    (selectedFamilyOrder I k).val < j.val ↔
      k.val < ((selectedFamilyOrder I).symm j).val := by
  change selectedFamilyOrder I k < j ↔ k < (selectedFamilyOrder I).symm j
  calc
    _ ↔ selectedFamilyOrder I k < selectedFamilyOrder I ((selectedFamilyOrder I).symm j) :=
      by rw [(selectedFamilyOrder I).apply_symm_apply j]
    _ ↔ k < (selectedFamilyOrder I).symm j := (selectedFamilyOrder I).lt_iff_lt

/-- Reindexing retains exactly the natural earlier prefix, not the full alphabet. -/
theorem selectedFamilyPrior_reindex (I : Finset ℕ) (K : I → Type*)
    [∀ i, AddCommGroup (K i)] (Φ : ∀ i, Point →+ K i) (j : I) (x : Point) :
    (Equiv.piCongrLeft K (selectedFamilyOrder I).toEquiv).symm
      (maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < j.val)) x) =
      finiteFamilyPriorHom (fun k => K (selectedFamilyOrder I k))
        (fun k => Φ (selectedFamilyOrder I k)) ((selectedFamilyOrder I).symm j).val x := by
  funext k
  simp only [Equiv.piCongrLeft_symm_apply]
  have hp : selectedFamilyOrder I k < j ↔ k < (selectedFamilyOrder I).symm j :=
    selectedFamilyOrder_prefix I j k
  simp [finiteFamilyPriorHom, maskedPriorHom, hp]

/-- The ACTUAL natural earlier-batch prior conditions the same experiment
as the existing newest-first finite observation history. -/
theorem selectedFamilyPrior_history_information {Ω S T : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (Y : Ω → S) (W : Ω → T) (j : I) :
    condMutualInfo Y W
      (fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < j.val)) (X ω)) μ =
      condMutualInfo Y W
        (observationHistory (fun n ω => finiteFamilyBatchHom
          (fun k => K (selectedFamilyOrder I k)) (fun k => Φ (selectedFamilyOrder I k)) n (X ω))
          ((selectedFamilyOrder I).symm j).val) μ := by
  let e := selectedFamilyOrder I
  let ψ := fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < j.val)) (X ω)
  have hi := condMutualInfo_of_inj (measurable_of_finite Y) (measurable_of_finite W)
    (measurable_of_finite ψ) μ (Equiv.piCongrLeft K e.toEquiv).symm.injective
  have he : (Equiv.piCongrLeft K e.toEquiv).symm ∘ ψ =
      fun ω => finiteFamilyPriorHom (fun k => K (e k)) (fun k => Φ (e k)) (e.symm j).val (X ω) := by
    funext ω
    exact selectedFamilyPrior_reindex I K Φ j (X ω)
  rw [he] at hi
  rw [← hi]
  exact finiteFamilyPrior_history_information (fun k => K (e k)) (fun k => Φ (e k))
    μ X Y W (e.symm j).val (Nat.le_of_lt (e.symm j).isLt)

/-- Faithful target embedding as well as the exact actual prior makes the
lower information experiment coincide with the upper word-history experiment. -/
theorem selectedFamilyBatch_history_information {Ω T : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (W : Ω → T) (k : Fin I.card) :
    let e := selectedFamilyOrder I
    condMutualInfo (fun ω => Φ (e k) (X ω)) W
      (fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < (e k).val)) (X ω)) μ =
      condMutualInfo
        (fun ω => finiteFamilyBatchHom (fun t => K (e t)) (fun t => Φ (e t)) k.val (X ω)) W
        (observationHistory (fun n ω => finiteFamilyBatchHom
          (fun t => K (e t)) (fun t => Φ (e t)) n (X ω)) k.val) μ := by
  dsimp only
  let e := selectedFamilyOrder I
  let K' := fun t => K (e t)
  let Y := fun ω => Φ (e k) (X ω)
  let Z := observationHistory (fun n ω => finiteFamilyBatchHom K' (fun t => Φ (e t)) n (X ω)) k.val
  have h := selectedFamilyPrior_history_information I K Φ μ X Y W (e k)
  rw [show (selectedFamilyOrder I).symm (e k) = k from
    (selectedFamilyOrder I).symm_apply_apply k] at h
  rw [h]
  symm
  have hi := condMutualInfo_of_inj_map (μ := μ) (measurable_of_finite Y)
    (measurable_of_finite W) (measurable_of_finite Z)
    (fun _ => familyCoordinateEmbed K' k) (fun _ => familyCoordinateEmbed_injective K' k)
  simpa [finiteFamilyBatchHom, k.isLt, familyCoordinateHom, Y, Z] using hi

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamilyOrder
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamilyOrder_prefix
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamilyPrior_reindex
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamilyPrior_history_information
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamilyBatch_history_information
