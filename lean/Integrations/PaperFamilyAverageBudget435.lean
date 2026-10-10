import Integrations.PaperFamilyAuxiliaryAverage435
import Integrations.SelectedFamilyWordBudget435
import Integrations.PaperFamilyWordLevels435
import Integrations.PaperTerminalLawMatch435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Average the concrete whole-family upper budget over the SAME genuine
auxiliary product, under the SAME original terminal law as the lower bound. -/
theorem PaperGridPositiveRateFamily.product_information_upper
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
    [∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, NeZero p.val]
    (z : ℕ → Point) (a : A → ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) 0)) [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) :
    let I := paperGeometricIndices f.natDegree M B
    let s := paperFamilyAuxiliaryRank f M B g0 a0 l m P
    let e := paperFamilyRootEquiv f hd R M B g0 c a0 l ε bad m P fam
    let F := fun (i : I) => labelledPrimeResidue (P i.val) (primeRootSet f) (e i)
    let μ := (paperFullTailLaw z f.natDegree M g0 a 0 ν).map
      (paperFullTailTerminalTime f.natDegree M g0 a 0)
    finiteUniformMean (fun choice : FamilyAuxiliaryChoice I P (Fin f.natDegree) s =>
      ∑ i : I,
        condMutualInfo (fun v => familyAuxiliaryHom I P (Fin f.natDegree) s F choice i (z v))
          (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ i.val)))
          (fun v => familyEarlierHom I P (familyAuxiliaryHom I P (Fin f.natDegree) s F choice) i.val (z v)) μ /
            rootWordLength f.natDegree (B ^ i.val)) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        paperGridSmoothingError f.natDegree M B (2 * Real.log (2 * (R + 1) + 1 : ℕ)) := by
  dsimp only
  let I := paperGeometricIndices f.natDegree M B
  let Q := Fin f.natDegree
  let s := paperFamilyAuxiliaryRank f M B g0 a0 l m P
  let e := paperFamilyRootEquiv f hd R M B g0 c a0 l ε bad m P fam
  let F := fun (i : I) => labelledPrimeResidue (P i.val) (primeRootSet f) (e i)
  let μ := (paperFullTailLaw z f.natDegree M g0 a 0 ν).map
    (paperFullTailTerminalTime f.natDegree M g0 a 0)
  let K := 2 * Real.log (2 * (R + 1) + 1 : ℕ)
  let cost := K + paperGridSmoothingError f.natDegree M B K
  let S := fun choice : FamilyAuxiliaryChoice I P Q s =>
    ∑ i : I,
      condMutualInfo (fun v => familyAuxiliaryHom I P Q s F choice i (z v))
        (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ i.val)))
        (fun v => familyEarlierHom I P (familyAuxiliaryHom I P Q s F choice) i.val (z v)) μ /
          rootWordLength f.natDegree (B ^ i.val)
  let : Nonempty Q := ⟨⟨0, by omega⟩⟩
  let : ∀ i : I, Nonempty (LabelledBatchChoice (P i.val) Q (s i)) :=
    fun i => paperFamilyAuxiliaryChoice_nonempty f hd R M B g0 c a0 l hl ε bad m P fam i
  have hT : 1 ≤ paperScheduleMaxT f.natDegree M := by
    unfold paperScheduleMaxT
    exact Real.one_le_exp (by have h := (paperScheduleX_pos f.natDegree M (by omega)).le; positivity)
  have hu : ∀ choice, S choice ≤ cost := by
    intro choice
    dsimp only [S, μ]
    rw [paperFullTailLaw_terminal_map]
    exact smoothedTimeLaw_selectedFamily_dyadic_budget I
      (fun i => (p : P i.val) → ZMod p.val) (familyAuxiliaryHom I P Q s F choice)
      _ _ z R hstep (fun i => rootWordLevel f.natDegree (B ^ i.val))
      (paperFamilyWordLevel_mono f.natDegree M B (by have := fam.margins.rootWords.covered.spacing; omega))
      (paperScheduleMaxT f.natDegree M) hT
      (fun i => paperGeometricIndices_word_le_max f.natDegree M B i.val (by omega)
        fam.margins.rootWords.covered.spacing i.property)
  have hmean := finiteUniformMean_mono S (fun _ => cost) hu
  rw [finiteUniformMean_const] at hmean
  exact hmean

/-- The actual walk has BOTH bounds on the same information average.
Neither a positive information rate nor an upper budget is assumed. -/
theorem PaperGridPositiveRateFamily.information_budget_sandwich
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (ha0 : 0 ≤ a0) (l : ℕ) (hl : 1 ≤ l)
    (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
    [∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, NeZero p.val]
    (z : ℕ → Point) (a : A → ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) 0)) [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) (hz : Function.Injective z)
    (havoid : ∀ i ∈ paperGeometricIndices f.natDegree M B, ∀ p ∈ P i, ∀ v,
      ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    paperJointRateConstant f.natDegree g0 a0 l * paperGeometricLogBudget f.natDegree M B ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        paperGridSmoothingError f.natDegree M B (2 * Real.log (2 * (R + 1) + 1 : ℕ)) :=
  (fam.product_information_lower f hf hd R M B g0 c a0 ha0 l hl ε bad m P z a ν hstep hz havoid).trans
    (fam.product_information_upper f hd R M B g0 c a0 l hl ε bad m P z a ν hstep)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridPositiveRateFamily.product_information_upper
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridPositiveRateFamily.information_budget_sandwich
