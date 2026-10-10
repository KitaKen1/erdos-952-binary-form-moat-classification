import Integrations.FinitePriorChain435
import Integrations.GeometricResidueAlphabet435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Each batch retains exactly its selected root residues; other coordinates
of that batch's fixed ambient alphabet are zero. -/
def familyBatchHom {ι : Type*} (P : ι → Finset ℕ)
    (φ : ∀ i, ∀ p : P i, Point →+ ZMod p.val) (C : ∀ i, Finset (P i)) (i : ι) :
    Point →+ ((p : P i) → ZMod p.val) :=
  maskedPriorHom (fun p : P i => ZMod p.val) (φ i) (C i)

/-- The actual earlier SELECTED batches, in one fixed finite ambient group.
No unselected root coordinate or later batch is revealed by this map. -/
def familyEarlierHom (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Φ : ∀ i : I, Point →+ ((p : P i.val) → ZMod p.val)) (j : ℕ) :
    Point →+ ((i : I) → (p : P i.val) → ZMod p.val) :=
  maskedPriorHom (fun i : I => (p : P i.val) → ZMod p.val) Φ
    (Finset.univ.filter (fun i : I => i.val < j))

theorem familyEarlierHom_selected (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Φ : ∀ i : I, Point →+ ((p : P i.val) → ZMod p.val)) (j : ℕ)
    (i : I) (hi : i.val < j) (x : Point) : familyEarlierHom I P Φ j x i = Φ i x := by
  simp [familyEarlierHom, maskedPriorHom, hi]

theorem familyEarlierHom_later (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (Φ : ∀ i : I, Point →+ ((p : P i.val) → ZMod p.val)) (j : ℕ)
    (i : I) (hi : j ≤ i.val) (x : Point) : familyEarlierHom I P Φ j x i = 0 := by
  simp [familyEarlierHom, maskedPriorHom, not_lt_of_ge hi]

/-- Any actual finite batch tuple pays at most its full prime alphabet.
This is only an entropy upper bound; no extra coordinates are conditioned on. -/
theorem primeBatchTuple_entropy_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (U : ℕ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P, p ≤ U) (X : Ω → ((p : P) → ZMod p.val)) :
    entropy X μ ≤ (P.card : ℝ) * Real.log U := by
  exact selected_prime_batch_entropy_le μ P P (fun _ h => h) U hU hP (fun p ω => X ω p)

/-- All actual smaller selected batch observations under ONE original law.
The full alphabets only bound their cost, and never replace the actual prior
inside conditional mutual information. -/
theorem familyEarlierHom_entropy_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ℕ) (P : ℕ → Finset ℕ) [∀ i : I, ∀ p : P i.val, NeZero p.val]
    (Φ : ∀ i : I, Point →+ ((p : P i.val) → ZMod p.val))
    (U : ℕ → ℕ) (hU : ∀ i ∈ I, 1 ≤ U i)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p ≤ U i) (j : ℕ) (X : Ω → Point) :
    entropy (fun ω => familyEarlierHom I P Φ j (X ω)) μ ≤
      ∑ i ∈ I.filter (fun i => i < j), ((P i).card : ℝ) * Real.log (U i) := by
  have h := entropy_pi_le_sum μ (fun i : I => (p : P i.val) → ZMod p.val)
    (fun i ω => familyEarlierHom I P Φ j (X ω) i) (fun _ => measurable_of_finite _)
  have hb : (∑ i : I, entropy (fun ω => familyEarlierHom I P Φ j (X ω) i) μ) ≤
      ∑ i : I, if i.val < j then ((P i.val).card : ℝ) * Real.log (U i.val) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i.val < j
    · simp only [hi, ↓reduceIte]
      have he : (fun ω => familyEarlierHom I P Φ j (X ω) i) = fun ω => Φ i (X ω) := by
        funext ω
        exact familyEarlierHom_selected I P Φ j i hi (X ω)
      rw [he]
      exact primeBatchTuple_entropy_le μ (P i.val) (U i.val) (hU i.val i.property)
        (hP i.val i.property) (fun ω => Φ i (X ω))
    · simp only [hi, ↓reduceIte]
      have he : (fun ω => familyEarlierHom I P Φ j (X ω) i) = fun _ : Ω => 0 := by
        funext ω
        exact familyEarlierHom_later I P Φ j i (by omega) (X ω)
      rw [he, entropy_const]
  apply (h.trans hb).trans_eq
  rw [Finset.sum_coe_sort I (fun i => if i < j then ((P i).card : ℝ) * Real.log (U i) else 0)]
  exact (Finset.sum_filter _ _).symm

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.familyBatchHom
#print axioms BinaryFormMoat.GeometryIntegration.familyEarlierHom
#print axioms BinaryFormMoat.GeometryIntegration.familyEarlierHom_selected
#print axioms BinaryFormMoat.GeometryIntegration.familyEarlierHom_later
#print axioms BinaryFormMoat.GeometryIntegration.primeBatchTuple_entropy_le
#print axioms BinaryFormMoat.GeometryIntegration.familyEarlierHom_entropy_le
