import Integrations.PaperCheckpointStop435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- T^r is expressed as exp(r log T), so later proofs use actual logarithms. -/
def paperCheckpointTarget (d : ℕ) (T : ℝ) (i : ℕ) : ℝ :=
  Real.exp (paperCheckpointRadius d i * Real.log T)

theorem paperCheckpointTarget_pos (d : ℕ) (T : ℝ) (i : ℕ) : 0 < paperCheckpointTarget d T i :=
  Real.exp_pos _

theorem paperCheckpointTarget_log (d : ℕ) (T : ℝ) (i : ℕ) :
    Real.log (paperCheckpointTarget d T i) = paperCheckpointRadius d i * Real.log T :=
  Real.log_exp _

/-- All checkpoint targets lie strictly inside the middle band, uniformly in i. -/
theorem paperCheckpointTarget_log_bounds (d m : ℕ) (hd : 1 ≤ d) (T : ℝ)
    (hlo : paperScheduleX d m ≤ Real.log T)
    (hhi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m) (i : ℕ) :
    (23 / 100 : ℝ) * (paperScheduleX d m / d) < Real.log (paperCheckpointTarget d T i) ∧
      Real.log (paperCheckpointTarget d T i) ≤ (21 / 80 : ℝ) * (paperScheduleX d m / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx := paperScheduleX_pos d m hd
  have hr := paperCheckpointRadius_bounds d i hd
  have hrP : 0 < paperCheckpointRadius d i := lt_trans (by positivity) hr.1
  have hLP : 0 < Real.log T := hx.trans_le hlo
  have hl := (mul_lt_mul_of_pos_right hr.1 hx).trans_le
    (mul_le_mul_of_nonneg_left hlo hrP.le)
  have hu := (mul_le_mul_of_nonneg_right hr.2 hLP.le).trans
    (mul_le_mul_of_nonneg_left hhi (show (0 : ℝ) ≤ 1 / (4 * d) by positivity))
  rw [paperCheckpointTarget_log]
  constructor
  · convert hl using 1; ring
  · convert hu using 1; ring

/-- ONE numerical threshold before g0, all selected windows, all batch values
and ALL checkpoint indices supplies each block and its recording ordinal. -/
theorem paperCheckpoint_uniform_middle_blocks (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m → ∀ (T g0 : ℝ),
      paperScheduleX d m ≤ Real.log T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m → ∀ i : ℕ,
        paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
          paperMiddleIterations M < paperBandOperationCount d M m g0 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (3 / (100 * d)) 4 (by positivity) 6
  refine ⟨max M0 1, ?_⟩
  intro M hM m hm T g0 hlo hhi i
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hs := (paperMiddle_iteration_span_le M hM1).trans
    (hM0 M ((le_max_left _ _).trans hM) m hm)
  have ht := paperCheckpointTarget_log_bounds d m hd T hlo hhi i
  have hx := paperScheduleX_pos d m hd
  have hg : 0 < paperScheduleMiddleG M := Real.exp_pos _
  have hg1 : paperScheduleMiddleG M < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hp : (0 : ℝ) < (M : ℝ) ^ 3 := by
      have h : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      positivity
    linarith
  have hvhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m 1 := by
    norm_num [paperBandHi, div_eq_mul_inv] at ht ⊢
    nlinarith [mul_pos hx (inv_pos.mpr hdR)]
  have hvlo : paperBandLo d m 1 +
      ((paperMiddleIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMiddleG M) ≤
        Real.log (paperCheckpointTarget d T i) := by
    norm_num [paperBandLo, div_eq_mul_inv] at hs ht ⊢
    linarith
  have hgmid : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  simpa only [paperBandOperationCount, hgmid] using
    paperBandEntry_block_fits (paperBandLo d m 1) (paperBandHi d m 1)
      (paperScheduleMiddleG M) (paperCheckpointTarget d T i) hg hg1 hvhi
      (paperMiddleIterations M) hvlo

/-- Reverse-target arithmetic: a log gap pays the one ceiling step and ALL
iterations, yielding a strict integer ordinal gap. -/
theorem paperBandEntry_separated (hi g V W : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hhi : Real.log V ≤ hi) (l : ℕ)
    (hgap : ((l : ℝ) + 1) * paperBandLogStep g ≤ Real.log V - Real.log W) :
    paperBandEntry hi g V + l < paperBandEntry hi g W := by
  have hs := paperBandLogStep_pos g hg hg1
  have hb := (paperBandEntry_log_bounds hi g V hg hg1 hhi).1
  have he : Real.log (paperBandScale (Real.exp hi) g (paperBandEntry hi g V)) =
      hi - (paperBandEntry hi g V : ℝ) * paperBandLogStep g := by
    rw [paperBandScale_log _ _ (Real.exp_pos _) hg, Real.log_exp,
      paperBandLogStep_eq_neg_log g hg]
    ring
  rw [he] at hb
  have hw := (div_le_iff₀ hs).mp (Nat.le_ceil ((hi - Real.log W) / paperBandLogStep g))
  change hi - Real.log W ≤ (paperBandEntry hi g W : ℝ) * paperBandLogStep g at hw
  have hn : ((paperBandEntry hi g V + l : ℕ) : ℝ) < paperBandEntry hi g W := by
    push_cast
    nlinarith
  exact_mod_cast hn

/-- The actual middle-grid recording ordinal is STRICTLY before the next
checkpoint for every i<J, independently of the walk or law. -/
theorem paperCheckpoint_middle_entry_gap (d M m : ℕ) (hd : 1 ≤ d) (T : ℝ) (hM : 2 ≤ M)
    (i : ℕ) (hi : i < paperCheckpointStop d M T (by omega))
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m 1) :
    paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
      paperMiddleIterations M <
        paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T (i + 1)) := by
  have hg : 0 < paperScheduleMiddleG M := Real.exp_pos _
  have hg1 : paperScheduleMiddleG M < 1 := by
    change Real.exp (-(M : ℝ) ^ 3) < 1
    rw [Real.exp_lt_one_iff]
    have hMP : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hp := pow_pos hMP 3
    linarith
  apply paperBandEntry_separated _ _ _ _ hg hg1 hhi
  rw [paperCheckpointTarget_log, paperCheckpointTarget_log]
  have h := paperCheckpoint_before_gap d M hd T hM i hi
  nlinarith

/-- Initial inventory is supplied uniformly: every middle target is <=cT/2.
The threshold precedes all indices, selected windows and batch values. -/
theorem paperCheckpoint_uniform_inventory_scale (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m → ∀ T : ℝ,
      0 < T → paperScheduleX d m ≤ Real.log T → ∀ i : ℕ,
        paperCheckpointTarget d T i ≤ (c / 2) * T := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdP : (0 : ℝ) < d := by linarith
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (3 / 4)
    (-Real.log (c / 2)) (by norm_num) 0
  refine ⟨M0, ?_⟩
  intro M hM m hm T hTP hT i
  have hs := hM0 M hM m hm
  simp only [pow_zero, mul_one] at hs
  have hx := paperScheduleX_pos d m hd
  have hLP : 0 < Real.log T := hx.trans_le hT
  have hr : paperCheckpointRadius d i ≤ 1 / 4 := by
    apply (paperCheckpointRadius_bounds d i hd).2.trans
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hprod := mul_le_mul_of_nonneg_right hr hLP.le
  have hl := mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  apply (Real.log_le_log_iff (paperCheckpointTarget_pos d T i) (by positivity)).mp
  rw [paperCheckpointTarget_log, Real.log_mul (by positivity) hTP.ne']
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointTarget
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointTarget_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointTarget_log
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointTarget_log_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_uniform_middle_blocks
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_separated
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_middle_entry_gap

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_uniform_inventory_scale
