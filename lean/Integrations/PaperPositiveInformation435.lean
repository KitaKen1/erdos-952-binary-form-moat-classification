import Integrations.PaperFamilyRate435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- The SAME actual chosen family has a positive auxiliary-averaged rate on
EVERY batch, with its actual earlier selected residues and original law.
No prior-entropy, bad-cost, quota, physical-cost or information bound is supplied. -/
theorem PaperGridPositiveRateFamily.positive_information_average
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (ha0 : 0 ≤ a0) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P)
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
      (a0 * (B ^ j : ℕ)) 0 (by have := (fam.margins.rootWords.covered.family.batches j hj).2.top.fit; omega)))
    :
    let I := paperGeometricIndices f.natDegree M B
    let Φ := familyBatchHom (fun i : I => P i.val) φ C
    let ψ := familyEarlierHom I P Φ j
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let u := paperFullTailTerminalTime f.natDegree M g0 a k
    let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
      (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
    let K := fun p : P j => ZMod p.val
    let F := labelledPrimeResidue (P j) (primeRootSet f) e
    paperJointRateConstant f.natDegree g0 a0 l / Real.log (B ^ j : ℕ) ≤
      (subsetLabelAverage s (fun C label =>
        condMutualInfo (fun v => maskedPriorHom K (fun p => F p (label p)) C (z v))
          (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
          (fun v => ψ (z v)) (μ.map u))) / rootWordLength f.natDegree (B ^ j) := by
  let batch := (fam.margins.rootWords.covered.family.batches j hj).2
  let T := B ^ j
  let L := rootWordLength f.natDegree T
  let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0 (a0 * T) l)
    (primeBatchLogMean (P j))
  let β := paperCheckpointBeta f.natDegree 0
  let K := paperPassingConstant (paperCoverageTau 0) β
  let c0 := paperJointRecordedConstant g0 a0 l
  let q := paperPassingCount T L (paperCoverageTau 0) β
  let loss := 4 * Real.log (2 * ((R + 1) * paperFutureShift
    (paperMiddleStartOp f M R (m j) g0 T 0 (P j) (batch.middle 0))) + 1 : ℕ)
  have hT : 2 ≤ T := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega)
    fam.margins.rootWords.covered.spacing hj
  have hTp : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hL : (0 : ℝ) < L := by exact_mod_cast rootWordLength_pos f.natDegree T
  have hb : 0 < β := paperCheckpointBeta_pos f.natDegree 0 (by omega)
  have hτ : 0 < paperCoverageTau 0 := by norm_num [paperCoverageTau]
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (paperPassingConstant_bounds (paperCoverageTau 0) β hτ hb.le).1
  have hq : (0 : ℝ) < q := by exact_mod_cast paperPassingCount_pos T L (paperCoverageTau 0) β
  have hlog : 0 < Real.log T := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hc0 : 0 ≤ c0 := by dsimp [c0, paperJointRecordedConstant]; positivity
  have hquota := paperPassingCount_upper T L hT (by have := rootWordLength_pos f.natDegree T; omega)
    (rootWordLength_le f.natDegree T (by omega) (by omega)) (paperCoverageTau 0) β hτ hb.le
  have hnum := mul_le_mul_of_nonneg_left batch.recorded_mass (by positivity : (0 : ℝ) ≤ β / 2)
  have hphysical := fam.physical j hj
  change loss ≤ paperJointRateConstant f.natDegree g0 a0 l * L / Real.log T at hphysical
  have hphysical' : loss ≤ β * c0 * L / (8 * K * Real.log T) := by
    convert hphysical using 1
    dsimp only [paperJointRateConstant, β, c0, K]
    ring
  have hi := fam.margins.rootWords.family_prior_half_beta_information f hf hd R M B g0 c a0 l hl ε
    bad m P j hj e φ C z a k ν hstep hz havoid hbefore fam.margins.accuracy (fam.margins.gap j hj)
  dsimp only [paperMiddleStartPosition] at hi
  rw [paperOpPosition_get _ (paperMiddleStartOp_mem f M R (m j)
    (fam.margins.rootWords.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j)
    (batch.middle 0))] at hi
  have hr := joint_quota_transport_normalized_rate β c0 T L K q (Real.log T)
    (β / 2 * ((s : ℝ) * primeBatchLogMean (P j))) loss _
    hb.le hc0 hTp hL hK hq hlog hquota hnum hphysical' hi
  convert hr using 1
  dsimp only [paperJointRateConstant, β, c0, K]
  ring

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridPositiveRateFamily.positive_information_average
