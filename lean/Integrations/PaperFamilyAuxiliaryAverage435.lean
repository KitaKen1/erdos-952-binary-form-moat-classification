import Integrations.FamilyAuxiliaryChoices435
import Integrations.PaperPositiveInformation435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

def paperFamilyAuxiliaryRank (f : Polynomial ℤ) (M B : ℕ) (g0 a0 : ℝ) (l : ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (i : paperGeometricIndices f.natDegree M B) : ℕ :=
  paperInputRank (paperBlockScale f.natDegree M (m i.val).val g0 0 (a0 * (B ^ i.val : ℕ)) l)
    (primeBatchLogMean (P i.val))

def paperFamilyRootEquiv (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (i : paperGeometricIndices f.natDegree M B) (p : P i.val) :
    Fin f.natDegree ≃ primeRootSet f p.val :=
  paperPrimeRootLabelEquiv f (P i.val) (fun p hp =>
    ((fam.margins.rootWords.covered.family.batches i.val i.property).2.primes p hp).2.2.2) p

/-- Every ACTUAL batch choice alphabet is nonempty by the derived top
recording inventory, with no supplied subset-capacity premise. -/
theorem paperFamilyAuxiliaryChoice_nonempty (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (i : paperGeometricIndices f.natDegree M B) :
    Nonempty (LabelledBatchChoice (P i.val) (Fin f.natDegree)
      (paperFamilyAuxiliaryRank f M B g0 a0 l m P i)) := by
  let : Nonempty (Fin f.natDegree) := ⟨⟨0, by omega⟩⟩
  apply labelledBatchChoice_nonempty
  exact (PaperJointBatch.record_inventory f R M (m i.val) g0 c a0 l (B ^ i.val) bad (P i.val)
    (fam.margins.rootWords.covered.family.batches i.val i.property).2 hl
    (paperGeometricIndices_scale_ge_two f.natDegree M B i.val (by omega)
      fam.margins.rootWords.covered.spacing i.property)).2

/-- The actual product of ALL subset/root choices supplies the sum lower
bound on ONE original terminal law. Auxiliary means stay outside entropy. -/
theorem PaperGridPositiveRateFamily.product_information_lower
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (ha0 : 0 ≤ a0) (l : ℕ) (hl : 1 ≤ l)
    (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
    [instP : ∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, NeZero p.val]
    (z : ℕ → Point) (a : A → ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) 0)) [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) (hz : Function.Injective z)
    (havoid : ∀ i ∈ paperGeometricIndices f.natDegree M B, ∀ p ∈ P i, ∀ v,
      ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    let I := paperGeometricIndices f.natDegree M B
    let s := paperFamilyAuxiliaryRank f M B g0 a0 l m P
    let e := paperFamilyRootEquiv f hd R M B g0 c a0 l ε bad m P fam
    let F := fun (i : I) => labelledPrimeResidue (P i.val) (primeRootSet f) (e i)
    let μ := (paperFullTailLaw z f.natDegree M g0 a 0 ν).map
      (paperFullTailTerminalTime f.natDegree M g0 a 0)
    paperJointRateConstant f.natDegree g0 a0 l * paperGeometricLogBudget f.natDegree M B ≤
      finiteUniformMean (fun choice : FamilyAuxiliaryChoice I P (Fin f.natDegree) s =>
        ∑ i : I,
          condMutualInfo (fun v => familyAuxiliaryHom I P (Fin f.natDegree) s F choice i (z v))
            (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ i.val)))
            (fun v => familyEarlierHom I P (familyAuxiliaryHom I P (Fin f.natDegree) s F choice) i.val (z v)) μ /
              rootWordLength f.natDegree (B ^ i.val)) := by
  dsimp only
  let I := paperGeometricIndices f.natDegree M B
  let Q := Fin f.natDegree
  let s := paperFamilyAuxiliaryRank f M B g0 a0 l m P
  let e := paperFamilyRootEquiv f hd R M B g0 c a0 l ε bad m P fam
  let F := fun (i : I) => labelledPrimeResidue (P i.val) (primeRootSet f) (e i)
  let μ := (paperFullTailLaw z f.natDegree M g0 a 0 ν).map
    (paperFullTailTerminalTime f.natDegree M g0 a 0)
  let : Nonempty Q := ⟨⟨0, by omega⟩⟩
  let : ∀ i : I, Nonempty (LabelledBatchChoice (P i.val) Q (s i)) :=
    fun i => paperFamilyAuxiliaryChoice_nonempty f hd R M B g0 c a0 l hl ε bad m P fam i
  have heq : paperJointRateConstant f.natDegree g0 a0 l * paperGeometricLogBudget f.natDegree M B =
      ∑ i : I, paperJointRateConstant f.natDegree g0 a0 l / Real.log (B ^ i.val : ℕ) := by
    rw [paperGeometricLogBudget, Finset.mul_sum]
    simp only [mul_one_div]
    exact (Finset.sum_coe_sort _ _).symm
  rw [heq]
  apply finiteUniformMean_product_sum_lower
  intro i choice
  rw [familyAuxiliary_information_refresh]
  let φ := fun (j : I) (p : P j.val) => F j p ((choice j).val.2 p)
  let C := fun j : I => (choice j).val.1
  let : ∀ p : P i.val, NeZero p.val := instP i
  have h := fam.positive_information_average f hf hd R M B g0 c a0 ha0 l hl ε bad m P
    i.val i.property (e i) φ C z a 0 ν hstep hz (havoid i.val i.property) (Nat.zero_le _)
  dsimp only at h
  rw [← subsetLabelAverage_div] at h
  exact h

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperFamilyAuxiliaryRank
#print axioms BinaryFormMoat.GeometryIntegration.paperFamilyRootEquiv
#print axioms BinaryFormMoat.GeometryIntegration.paperFamilyAuxiliaryChoice_nonempty
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridPositiveRateFamily.product_information_lower
