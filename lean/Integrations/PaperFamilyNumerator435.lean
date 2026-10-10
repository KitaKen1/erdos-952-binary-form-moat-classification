import Integrations.PaperFamilyPriorInformation435
import Integrations.JointInformationMargin435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- The actual chosen family's joint numerator retains at least beta*H/2
once fixed accuracy and list-cost scalar thresholds hold. Prior entropy and
backward-coverage losses are derived, never supplied information premises.
The physical transport loss remains explicit until its uniform absorption. -/
theorem PaperGridRootWordFamily.family_prior_half_beta_information
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
      (a0 * (B ^ j : ℕ)) 0 (by have := (fam.covered.family.batches j hj).2.top.fit; omega)))
    (haccuracy : 90 * g0 + (1 / 2 : ℝ) ^ l + ε ≤ paperCheckpointBeta f.natDegree 0 / 4)
    (hgap : Real.log 6 ≤ paperCheckpointBeta f.natDegree 0 * Real.log (B ^ j : ℕ) / 8) :
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
    (((β / 2) * ((s : ℝ) * primeBatchLogMean (P j))) /
        paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β -
      4 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)) ≤
      subsetLabelAverage s (fun C label =>
        condMutualInfo (fun v => maskedPriorHom K (fun p => F p (label p)) C (z v))
          (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
          (fun v => ψ (z v)) (μ.map u)) := by
  let batch := (fam.covered.family.batches j hj).2
  let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
  have hq : q < (paperScheduleList f.natDegree M g0).length :=
    paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
      (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
  let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
    (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
  let β := paperCheckpointBeta f.natDegree 0
  let loss := 4 * Real.log (2 * ((R + 1) * paperFutureShift
    ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)
  have hT := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) fam.covered.spacing hj
  have hL := primeBatchLogMean_dyadic_bounds (P j) (B ^ j) hT batch.nonempty
    (fun p hp => (batch.primes p hp).2.1) (fun p hp => (batch.primes p hp).2.2.1)
  have hβ : 0 ≤ β := (paperCheckpointBeta_pos _ _ (by omega)).le
  have hgap' : Real.log 6 ≤ β * primeBatchLogMean (P j) / 8 :=
    hgap.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.2.1 hβ) (by norm_num))
  have hn := beta_joint_numerator_margin β (90 * g0 + (1 / 2 : ℝ) ^ l) ε s
    (primeBatchLogMean (P j)) (Real.log (2 * B ^ j : ℕ)) hβ (Nat.cast_nonneg _) hL.1.le
    haccuracy hgap' hL.2.2.2
  have hi := fam.family_prior_information_average f hf hd R M B g0 c a0 l hl ε bad m P j hj e
    φ C z a k ν hstep hz havoid hbefore
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hn
    (show (0 : ℝ) ≤ paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j))
      (paperCoverageTau 0) β from Nat.cast_nonneg _)) loss).trans hi

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.family_prior_half_beta_information
