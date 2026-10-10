import Integrations.PaperBackwardCoverage435
import Integrations.GeometricBatches435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- One actual prime set carries every band certificate. In particular, the
top entropy and the backward coverage never select different prime sets. -/
structure PaperJointBatch (f : Polynomial ℤ) (R M : ℕ) (m : Fin (M + 1))
    (g0 c a0 : ℝ) (l T : ℕ) (bad P : Finset ℕ) : Prop where
  card_eq : P.card = paperPrimeCount c T
  excluded : Disjoint P bad
  primes : ∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree
  nonempty : 0 < P.card
  alphabet : (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T
  top : PaperBlockCertificate f R M m g0 0 (a0 * T) l P
  middle : ∀ i : ℕ, PaperBlockCertificate f R M m g0 1
    (paperCheckpointTarget f.natDegree T i) (paperMiddleIterations M) P
  bottom : PaperBlockCertificate f R M m g0 2
    (paperBottomTarget f.natDegree m.val) (paperBottomIterations M) P
  recorded_mass : (((g0 ^ 2) ^ (l + 1) * a0) / 2) * T ≤
    (paperInputRank (paperBlockScale f.natDegree M m.val g0 0 (a0 * T) l)
      (primeBatchLogMean P) : ℝ) * primeBatchLogMean P

/-- Fixed constants and ONE threshold supply the SAME floor-sized batch
for every band, every admissible scale and every walk-independent exclusion. -/
theorem paperSchedule_joint_batches (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∀ M ≥ M0,
        ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℕ, 2 ≤ T →
          paperScheduleX f.natDegree m.val ≤ Real.log T →
          Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
          ∃ P : Finset ℕ, PaperJointBatch f R M m g0 c a0 l T bad P := by
  obtain ⟨c, hc, hsupply⟩ := exists_paper_prime_inventory f hf hd
  let a0 := min (c / 2) 1
  have ha0 : 0 < a0 := lt_min (by positivity) (by norm_num)
  have ha01 : a0 ≤ 1 := min_le_right _ _
  have ha0c : a0 ≤ c / 2 := min_le_left _ _
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l bad
  obtain ⟨T0, hT0⟩ := (hsupply bad).exists_forall_of_atTop
  obtain ⟨Mt, ht⟩ := paperSchedule_uniform_batch_threshold f.natDegree (by omega) T0
  obtain ⟨Mi, hi⟩ := paperSchedule_block_certificate_threshold f R (by omega) g0 hg0 hg064
  obtain ⟨Mm, hmfit⟩ := paperCheckpoint_uniform_middle_blocks f.natDegree (by omega)
  obtain ⟨Mb, hbfit⟩ := paperBottom_uniform_blocks f.natDegree (by omega)
  obtain ⟨Mc, hscale⟩ := paperCheckpoint_uniform_inventory_scale f.natDegree (by omega) c hc
  obtain ⟨Mr, hroom⟩ := paperSchedule_top_block_fits f.natDegree (by omega) a0 g0
    ha0 ha01 hg0 (by linarith) l
  obtain ⟨Mq, hmass⟩ := paperSchedule_top_record_mass f.natDegree (by omega) a0 g0
    ha0 ha01 hg0 (by linarith) l
  refine ⟨Mt + Mi + Mm + Mb + Mc + Mr + Mq, ?_⟩
  intro M hM m hm T hT hlo hhi
  obtain ⟨P, hPc, hbad, hP, hPk, hcap, _, hAlpha, _⟩ :=
    hT0 T (ht M (by omega) m.val hm T hlo)
  have hPl : ∀ p ∈ P, T ≤ p := fun p hp => (hP p hp).2.1
  have hPh : ∀ p ∈ P, p ≤ 2 * T := fun p hp => (hP p hp).2.2.1
  have hmid : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  have hvhi (i : ℕ) : Real.log (paperCheckpointTarget f.natDegree T i) ≤
      paperBandHi f.natDegree m.val 1 := by
    have hs := (paperCheckpointTarget_log_bounds f.natDegree m.val (by omega) T hlo hhi i).2
    have hdR : (0 : ℝ) < f.natDegree := by exact_mod_cast (by omega : 0 < f.natDegree)
    norm_num [paperBandHi, div_eq_mul_inv] at hs ⊢
    nlinarith [mul_pos (paperScheduleX_pos f.natDegree m.val (by omega)) (inv_pos.mpr hdR)]
  have htarget (i : ℕ) : paperCheckpointTarget f.natDegree T i ≤ (c / 2) * T :=
    hscale M (by omega) m.val hm T (by exact_mod_cast (by omega : 0 < T)) hlo i
  have hVhi : Real.log (a0 * T) ≤ paperBandHi f.natDegree m.val 0 := by
    rw [Real.log_mul ha0.ne' (by exact_mod_cast (by omega : T ≠ 0))]
    have ha : Real.log a0 ≤ 0 := Real.log_nonpos ha0.le ha01
    have hx := (paperScheduleX_pos f.natDegree m.val (by omega)).le
    simp only [paperBandHi, ↓reduceIte]
    linarith
  refine ⟨P, hPc, hbad, hP, hPk, hAlpha, ?_, ?_, ?_, ?_⟩
  · apply hi M (by omega) m hm T P hT hPk hPl hPh hhi 0 (a0 * T) c l
      (by positivity) hVhi
    · simpa only [paperBandG, ↓reduceIte] using hroom M (by omega) m.val hm T hT hlo hhi
    · exact mul_le_mul_of_nonneg_right ha0c (Nat.cast_nonneg _)
    · exact hcap
  · intro i
    apply hi M (by omega) m hm T P hT hPk hPl hPh hhi 1 _ c (paperMiddleIterations M)
      (paperCheckpointTarget_pos _ _ _) (hvhi i)
    · simpa only [hmid] using hmfit M (by omega) m.val hm T g0 hlo hhi i
    · exact htarget i
    · exact hcap
  · apply hi M (by omega) m hm T P hT hPk hPl hPh hhi 2 _ c (paperBottomIterations M)
      (Real.exp_pos _) (by simp) (hbfit M (by omega) m.val hm g0)
    · exact (paperBottomTarget_le_checkpoint_zero f.natDegree m.val (by omega) T hlo).trans (htarget 0)
    · exact hcap
  · simpa only [paperBlockScale, paperBandG, ↓reduceIte] using
      hmass M (by omega) m.val hm T hT hlo hhi P hPk hPl hPh

/-- The recorded top rank is positive and inside the actual joint batch. -/
theorem PaperJointBatch.record_inventory (f : Polynomial ℤ) (R M : ℕ) (m : Fin (M + 1))
    (g0 c a0 : ℝ) (l T : ℕ) (bad P : Finset ℕ)
    (batch : PaperJointBatch f R M m g0 c a0 l T bad P) (hl : 1 ≤ l) (hT : 2 ≤ T) :
    0 < paperInputRank (paperBlockScale f.natDegree M m.val g0 0 (a0 * T) l)
      (primeBatchLogMean P) ∧
    paperInputRank (paperBlockScale f.natDegree M m.val g0 0 (a0 * T) l)
      (primeBatchLogMean P) ≤ P.card := by
  have hL := primeBatchLogMean_dyadic_bounds P T hT batch.nonempty
    (fun p hp => (batch.primes p hp).2.1) (fun p hp => (batch.primes p hp).2.2.1)
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans hL.2.1
  simpa only [paperBlockScale] using paperInventoryBlock_record_inventory f (R + 1) M m.val g0
    0 (a0 * T) l P hl hL.1 hL2 batch.top.inputs

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_joint_batches
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.record_inventory
