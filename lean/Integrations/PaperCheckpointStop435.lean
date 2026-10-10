import Integrations.PaperCheckpointParameters435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

theorem paperCheckpointStop_le_of_bound (d M : ℕ) (T : ℝ) (hM : 1 ≤ M) (i : ℕ)
    (hi : paperCheckpointBeta d i * Real.log T ≤ (M : ℝ) ^ 20) :
    paperCheckpointStop d M T hM ≤ i :=
  Nat.find_min' (paperCheckpoint_exists_stop d M T hM) hi

/-- A coarse explicit linear bound replaces the paper's J=O(M). -/
theorem paperCheckpointStop_linear_bound (d M : ℕ) (hd : 1 ≤ d) (T : ℝ) (hM : 1 ≤ M)
    (hlog : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M) :
    paperCheckpointStop d M T hM ≤ (100 * d) * M := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdP : (0 : ℝ) < d := by linarith
  have hb : paperScheduleBase d ≤ (2 : ℝ) ^ (100 * d) := by
    unfold paperScheduleBase
    exact_mod_cast (show 100 * d ≤ 2 ^ (100 * d) from Nat.lt_two_pow_self.le)
  have hc : (1 / 2 : ℝ) ^ (100 * d) * paperScheduleBase d ≤ 1 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (100 * d) * (2 : ℝ) ^ (100 * d) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hx : (1 / 2 : ℝ) ^ ((100 * d) * M) * paperScheduleX d M ≤ 1 := by
    rw [pow_mul, paperScheduleX, ← mul_pow]
    exact pow_le_one₀ (by unfold paperScheduleBase; positivity) hc
  have hcoef : (21 / 20 : ℝ) / (200 * d) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  apply paperCheckpointStop_le_of_bound
  calc
    _ ≤ ((1 / 2 : ℝ) ^ ((100 * d) * M) / (200 * d)) *
        ((21 / 20 : ℝ) * paperScheduleX d M) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = ((21 / 20 : ℝ) / (200 * d)) *
        ((1 / 2 : ℝ) ^ ((100 * d) * M) * paperScheduleX d M) := by ring
    _ ≤ (21 / 20 : ℝ) / (200 * d) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx
        (show (0 : ℝ) ≤ (21 / 20 : ℝ) / (200 * d) by positivity)
    _ ≤ 1 := hcoef
    _ ≤ (M : ℝ) ^ 20 := one_le_pow₀ (by exact_mod_cast hM)

/-- Choose ONE threshold before all selected windows and batch values. -/
theorem paperCheckpoint_uniform_start (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m → ∀ T : ℝ,
      paperScheduleX d m ≤ Real.log T →
        (M : ℝ) ^ 20 < paperCheckpointBeta d 0 * Real.log T := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (1 / (400 * d)) 1 (by positivity) 20
  refine ⟨M0, ?_⟩
  intro M hM m hm T hT
  have hs := hM0 M hM m hm
  have hx := paperScheduleX_pos d m hd
  have hl := mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ 1 / (200 * d) by positivity)
  norm_num [paperCheckpointBeta, div_eq_mul_inv] at hs hl ⊢
  nlinarith [mul_pos (inv_pos.mpr hdR) hx]

/-- The actual middle block consumes at most 4M^6, including its ceiling step. -/
theorem paperMiddle_iteration_span_le (M : ℕ) (hM : 1 ≤ M) :
    ((paperMiddleIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMiddleG M) ≤
      4 * (M : ℝ) ^ 6 := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : 1 ≤ (M : ℝ) ^ 3 := one_le_pow₀ hMR
  have he : ((M : ℝ) ^ 3) ^ 2 = (M : ℝ) ^ 6 := by ring
  rw [paperScheduleMiddle_logStep]
  simp only [paperMiddleIterations, Nat.cast_pow]
  nlinarith

theorem paperMiddle_span_le_stop_gap (M : ℕ) (hM : 2 ≤ M) :
    ((paperMiddleIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMiddleG M) ≤
      2 * (M : ℝ) ^ 20 := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (M : ℝ) ≤ (M : ℝ) ^ 14 := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ M) (by norm_num : 1 ≤ 14)
  have he : (M : ℝ) ^ 20 = (M : ℝ) ^ 6 * (M : ℝ) ^ 14 := by ring
  apply (paperMiddle_iteration_span_le M (by omega)).trans
  nlinarith [pow_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) 6]

/-- Before stopping, every joint-entropy block fits in the strict log gap to
its next checkpoint, using the actual M^3 iterations. -/
theorem paperCheckpoint_before_gap (d M : ℕ) (hd : 1 ≤ d) (T : ℝ) (hM : 2 ≤ M)
    (i : ℕ) (hi : i < paperCheckpointStop d M T (by omega)) :
    ((paperMiddleIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMiddleG M) <
      (paperCheckpointRadius d i - paperCheckpointRadius d (i + 1)) * Real.log T := by
  have hb := paperCheckpointStop_before d M T (by omega) i hi
  have hs := paperMiddle_span_le_stop_gap M hM
  rw [paperCheckpointRadius_succ d i hd]
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_le_of_bound
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_linear_bound
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_uniform_start
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_iteration_span_le
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_span_le_stop_gap
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_before_gap
