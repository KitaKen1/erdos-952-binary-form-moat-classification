import Integrations.FiniteNaturalCheckpoint435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Canonical actual start selected by a constructed middle certificate. -/
def paperMiddleStartOp (f : Polynomial ℤ) (M R : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) : PaperScheduleOp f.natDegree M g0 :=
  paperBlockOp g0 m 1 (paperCheckpointTarget f.natDegree T i) 0 (by have := cert.fit; omega)

def paperMiddleStartPosition (f : Polynomial ℤ) (M R : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) : ℕ := paperOpPosition (paperMiddleStartOp f M R m g0 T i P cert)

def paperMiddleRecordRank (f : Polynomial ℤ) (M : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ) : ℕ :=
  paperInputRank (paperBlockScale f.natDegree M m.val g0 1 (paperCheckpointTarget f.natDegree T i)
    (paperMiddleIterations M)) (primeBatchLogMean P)

theorem paperMiddleStartOp_mem (f : Polynomial ℤ) (M R : ℕ) (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T i : ℕ) (P : Finset ℕ)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) :
    paperMiddleStartOp f M R m g0 T i P cert ∈ paperScheduledOps f.natDegree M g0 :=
  paperBlockOp_mem g0 m hm 1 _ 0 _

theorem paperMiddleStartOp_eq_checkpoint (f : Polynomial ℤ) (M R : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) :
    paperMiddleStartOp f M R m g0 T i P cert =
      paperMiddleCheckpointOp g0 m T i (by
        have h := cert.fit
        simp [paperBandG] at h
        omega) := by
  simp [paperMiddleStartOp, paperBlockOp, paperMiddleCheckpointOp, paperBandG]

/-- The recording rank is a genuine nonempty subset size in the SAME prime
inventory. No rank positivity or capacity premise is added to the transfer. -/
theorem paperMiddleRecordRank_bounds (f : Polynomial ℤ) (M R : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ) (hM : 1 ≤ M)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) :
    1 ≤ paperMiddleRecordRank f M m g0 T i P ∧ paperMiddleRecordRank f M m g0 T i P ≤ P.card := by
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  exact paperInventoryBlock_record_inventory f (R + 1) M m.val g0 1
    (paperCheckpointTarget f.natDegree T i) (paperMiddleIterations M) P
    (by change 1 ≤ M ^ 3; exact one_le_pow₀ hM) hL hL2 cert.inputs

/-- Every target's log is inside its actual band, so the earlier entropy
and native-alphabet adapters have no extra target-location hypothesis. -/
theorem paperMiddleTarget_log_hi (d m : ℕ) (hd : 1 ≤ d) (T : ℝ)
    (hlo : paperScheduleX d m ≤ Real.log T)
    (hhi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m) (i : ℕ) :
    Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m 1 := by
  have h := (paperCheckpointTarget_log_bounds d m hd T hlo hhi i).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  norm_num [paperBandHi, div_eq_mul_inv] at h ⊢
  nlinarith [mul_pos (paperScheduleX_pos d m hd) (inv_pos.mpr hdR)]

/-- The actual start's full native future alphabet fits C_R*T^r_i.
Only the already uniformly supplied all-operation future bound is used. -/
theorem paperMiddleStart_native_alphabet (f : Polynomial ℤ) (hd : 1 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T i : ℕ) (P : Finset ℕ)
    (hT : 2 ≤ T) (hlo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hhi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (hfuture : ∀ o ∈ paperScheduledOps f.natDegree M g0,
      Real.log (paperFutureShift o + 1 : ℕ) ≤ 2 * (paperOpG o * paperOpU o)) :
    2 * Real.log (2 * ((R + 1) * paperFutureShift (paperMiddleStartOp f M R m g0 T i P cert)) + 1 : ℕ) ≤
      (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) * paperCheckpointTarget f.natDegree T i := by
  have hmemb := paperMiddleStartOp_mem f M R m hm g0 T i P cert
  have hg1 : paperScheduleMiddleG M < 1 := by
    have h := cert.inputs.g_small
    simp [paperBandG] at h
    linarith
  have hloc := paperMiddleTarget_log_hi f.natDegree m.val hd (T : ℝ) hlo hhi i
  have htarget : 1 ≤ paperCheckpointTarget f.natDegree T i := by
    apply Real.one_le_exp_iff.mpr
    have hr := (paperCheckpointRadius_bounds f.natDegree i hd).1
    have hdR : (0 : ℝ) < f.natDegree := by exact_mod_cast (show 0 < f.natDegree by omega)
    have hrP : 0 < paperCheckpointRadius f.natDegree i := lt_trans (by positivity) hr
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < T by omega))
    positivity
  have hfut := hfuture _ hmemb
  rw [paperMiddleStartOp_eq_checkpoint] at hfut ⊢
  exact paperMiddleCheckpoint_native_alphabet g0 m T i R _ hg1 hloc htarget hfut

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleStartOp
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleStartPosition
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleRecordRank
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleStartOp_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleStartOp_eq_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleRecordRank_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleTarget_log_hi
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleStart_native_alphabet
