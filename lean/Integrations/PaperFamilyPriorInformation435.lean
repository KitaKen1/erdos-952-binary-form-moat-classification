import Integrations.FamilyResiduePrior435
import Integrations.PaperJointInformationAverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- The SAME chosen family pays for its actual smaller SELECTED residue
observations. Valid for every original finite law and every auxiliary choice;
no supplied prior entropy or information bound is used. -/
theorem PaperGridRootWordFamily.earlier_prior_entropy
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree) (R M B : ℕ) (g0 c a0 : ℝ)
    (l : ℕ) (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    [∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, NeZero p.val]
    (φ : ∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, Point →+ ZMod p.val)
    (C : ∀ i : paperGeometricIndices f.natDegree M B, Finset (P i.val))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Point) :
    let I := paperGeometricIndices f.natDegree M B
    let Φ := familyBatchHom (fun i : I => P i.val) φ C
    entropy (fun ω => familyEarlierHom I P Φ j (X ω)) μ ≤
      ε * ((paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
        (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j)) : ℝ) * primeBatchLogMean (P j)) := by
  let I := paperGeometricIndices f.natDegree M B
  let Φ := familyBatchHom (fun i : I => P i.val) φ C
  have h := familyEarlierHom_entropy_le μ I P Φ (fun i => 2 * B ^ i)
    (by intro i _; have hB := fam.covered.spacing; have := pow_pos (by omega : 0 < B) i; omega)
    (by intro i hi p hp; exact ((fam.covered.family.batches i hi).2.primes p hp).2.2.1) j X
  exact h.trans (fam.covered.family.smaller_alphabet j hj)

/-- The actual selected-family prior is now instantiated and its entropy
cost is paid by the SAME family's smaller-alphabet certificate. Current
subset/root choices remain averaged outside the ORIGINAL terminal law. -/
theorem PaperGridRootWordFamily.family_prior_information_average
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    [instP : ∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, NeZero p.val]
    [∀ p : P j, NeZero p.val] (e : ∀ p : P j, Q ≃ primeRootSet f p.val)
    (φ : ∀ i : paperGeometricIndices f.natDegree M B, ∀ p : P i.val, Point →+ ZMod p.val)
    (C : ∀ i : paperGeometricIndices f.natDegree M B, Finset (P i.val))
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) (hz : Function.Injective z)
    (havoid : ∀ p ∈ P j, ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs)
    (hbefore : k ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 (m j) 0
      (a0 * (B ^ j : ℕ)) 0 (by have := (fam.covered.family.batches j hj).2.top.fit; omega))) :
    let I := paperGeometricIndices f.natDegree M B
    let Φ := familyBatchHom (fun i : I => P i.val) φ C
    let ψ := familyEarlierHom I P Φ j
    let batch := (fam.covered.family.batches j hj).2
    let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
    let hq : q < (paperScheduleList f.natDegree M g0).length :=
      paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
        (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let u := paperFullTailTerminalTime f.natDegree M g0 a k
    let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
      (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
    let β := paperCheckpointBeta f.natDegree 0
    let K := fun p : P j => ZMod p.val
    let F := labelledPrimeResidue (P j) (primeRootSet f) e
    (((β - (90 * g0 + (1 / 2 : ℝ) ^ l) - ε) * ((s : ℝ) * primeBatchLogMean (P j)) -
      s * Real.log 6 -
      2 * paperCoverageEta 0 * s * Real.log (2 * B ^ j : ℕ) * β) /
        paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β -
      4 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)) ≤
      subsetLabelAverage s (fun C label =>
        condMutualInfo (fun v => maskedPriorHom K (fun p => F p (label p)) C (z v))
          (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
          (fun v => ψ (z v)) (μ.map u)) := by
  let I := paperGeometricIndices f.natDegree M B
  let Φ := familyBatchHom (fun i : I => P i.val) φ C
  let ψ := familyEarlierHom I P Φ j
  let batch := (fam.covered.family.batches j hj).2
  let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
  have hq : q < (paperScheduleList f.natDegree M g0).length :=
    paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
      (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
  let μ := paperFullTailLaw z f.natDegree M g0 a k ν
  let r := paperFullTailCheckpointTime f.natDegree M g0 a k q hq.le
  let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
    (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
  let β := paperCheckpointBeta f.natDegree 0
  let loss := 4 * Real.log (2 * ((R + 1) * paperFutureShift
    ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)
  have hO := fam.earlier_prior_entropy f hd R M B g0 c a0 l ε bad m P j hj φ C μ
    (fun ω => z (r ω))
  have hi := fam.joint_information_average f hf hd R M B g0 c a0 l hl ε bad m P
    j hj e z a k ν hstep hz ψ havoid hbefore
  dsimp only at hi
  have hnum : (β - (90 * g0 + (1 / 2 : ℝ) ^ l) - ε) *
      ((s : ℝ) * primeBatchLogMean (P j)) - s * Real.log 6 -
        2 * paperCoverageEta 0 * s * Real.log (2 * B ^ j : ℕ) * β ≤
      (β - (90 * g0 + (1 / 2 : ℝ) ^ l)) * ((s : ℝ) * primeBatchLogMean (P j)) -
        entropy (fun ω => ψ (z (r ω))) μ - s * Real.log 6 -
        2 * paperCoverageEta 0 * s * Real.log (2 * B ^ j : ℕ) * β := by
    change entropy (fun ω => ψ (z (r ω))) μ ≤ ε * ((s : ℝ) * primeBatchLogMean (P j)) at hO
    nlinarith only [hO]
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hnum
    (show (0 : ℝ) ≤ paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j))
      (paperCoverageTau 0) β from Nat.cast_nonneg _)) loss).trans hi

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.earlier_prior_entropy
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.family_prior_information_average
