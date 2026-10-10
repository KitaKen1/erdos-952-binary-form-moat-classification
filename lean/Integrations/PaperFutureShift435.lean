import Integrations.PaperScheduleOrder435
import Integrations.TerminalSchedule435
import Integrations.WalkLaw435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- The extremal transition weight dominates every fixed power of X_M. -/
theorem tendsto_paperSchedule_weight_over_Xpow (d k : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun M => paperScheduleMinG M * paperScheduleMinU d M /
      paperScheduleX d M ^ k) atTop atTop := by
  let b := Real.log (paperScheduleBase d)
  let a := b / 2
  let c := 1 / (20 * (d : ℝ))
  have hb : 0 < b := Real.log_pos (paperScheduleBase_gt_one d hd)
  have ha : 0 < a := by dsimp [a]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr := (tendsto_double_exponential_ratio a c 100 (k * b) 20 ha hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop_mono _ hr
  intro M
  have hU : Real.exp (c * Real.exp (a * M)) ≤ paperScheduleMinU d M := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right (paperScheduleX_half_lower d M hd)
      (show (0 : ℝ) ≤ 20 * d by positivity)
    simpa [c, a, b, div_eq_mul_inv, mul_comm] using h
  have hx : paperScheduleX d M ^ k = Real.exp ((k * b) * M) := by
    rw [paperScheduleX_exp d M hd, ← Real.exp_nat_mul]
    congr 1
    dsimp [b]
    ring
  dsimp [Function.comp_def]
  rw [hx]
  change Real.exp (-100 * (M : ℝ) ^ 20) * _ / _ ≤
    Real.exp (-100 * (M : ℝ) ^ 20) * paperScheduleMinU d M / _
  gcongr

/-- The terminal ceiling length has a coarse exponential envelope. -/
theorem paperTerminalLength_le_exp (d M : ℕ) (hd : 1 ≤ d) :
    (terminalSmoothingLength (paperScheduleMaxT d M) : ℝ) ≤
      Real.exp (20 * paperScheduleX d M) := by
  have hx := paperScheduleX_ge_count d M hd
  have hx1 : 1 ≤ paperScheduleX d M := by
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hT : 0 < paperScheduleMaxT d M := Real.exp_pos _
  rw [terminalSmoothingLength_eq_ceil _ hT]
  have hc := (Nat.ceil_lt_add_one (pow_nonneg hT.le 10)).le
  have hp : paperScheduleMaxT d M ^ 10 = Real.exp ((21 / 2 : ℝ) * paperScheduleX d M) := by
    unfold paperScheduleMaxT
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp] at hc ⊢
  have he1 : 1 ≤ Real.exp ((21 / 2 : ℝ) * paperScheduleX d M) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have he2 : 2 ≤ Real.exp (paperScheduleX d M) := by
    linarith [Real.add_one_le_exp (paperScheduleX d M)]
  calc
    _ ≤ Real.exp ((21 / 2 : ℝ) * paperScheduleX d M) + 1 := hc
    _ ≤ Real.exp ((21 / 2 : ℝ) * paperScheduleX d M) * Real.exp (paperScheduleX d M) := by
      nlinarith
    _ = Real.exp ((23 / 2 : ℝ) * paperScheduleX d M) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Exact manuscript bound: final offset N-1 plus every current/future window.
All terms are fixed before any starting law or exact start is chosen. -/
def paperFutureShift {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0) : ℕ :=
  terminalSmoothingLength (paperScheduleMaxT d M) - 1 +
    ∑ b ∈ (paperScheduledOps d M g0).filter (paperOpLater a), paperWalkWindow (paperOpU b) (paperOpG b)

/-- A scalar sum envelope. Every listed future window is charged once. -/
theorem paperFutureShift_log_bound {d M : ℕ} {g0 : ℝ}
    (a : PaperScheduleOp d M g0)
    (hweight : ∀ b ∈ (paperScheduledOps d M g0).filter (paperOpLater a),
      paperOpG b * paperOpU b ≤ paperOpG a * paperOpU a)
    (hN : (terminalSmoothingLength (paperScheduleMaxT d M) : ℝ) ≤
      Real.exp (paperOpG a * paperOpU a))
    (hcard : ((paperScheduledOps d M g0).card : ℝ) + 1 ≤
      Real.exp (paperOpG a * paperOpU a)) :
    Real.log (paperFutureShift a + 1 : ℕ) ≤ 2 * (paperOpG a * paperOpU a) := by
  let s := (paperScheduledOps d M g0).filter (paperOpLater a)
  have hsum : (∑ b ∈ s, (paperWalkWindow (paperOpU b) (paperOpG b) : ℝ)) ≤
      (s.card : ℝ) * Real.exp (paperOpG a * paperOpU a) := by
    calc
      _ ≤ ∑ _b ∈ s, Real.exp (paperOpG a * paperOpU a) := by
        apply Finset.sum_le_sum
        intro b hb
        exact (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr (hweight b hb))
      _ = _ := by simp
  have hscard : (s.card : ℝ) ≤ (paperScheduledOps d M g0).card := by
    exact_mod_cast Finset.card_filter_le (paperScheduledOps d M g0) (paperOpLater a)
  have heq : paperFutureShift a + 1 = terminalSmoothingLength (paperScheduleMaxT d M) +
      ∑ b ∈ s, paperWalkWindow (paperOpU b) (paperOpG b) := by
    have hp := terminalSmoothingLength_pos (paperScheduleMaxT d M)
    unfold paperFutureShift
    dsimp [s]
    omega
  have hbound : ((paperFutureShift a + 1 : ℕ) : ℝ) ≤
      Real.exp (2 * (paperOpG a * paperOpU a)) := by
    rw [heq]
    push_cast
    have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hscard (Real.exp_pos _).le)
    calc
      _ ≤ (((paperScheduledOps d M g0).card : ℝ) + 1) * Real.exp (paperOpG a * paperOpU a) := by
        nlinarith
      _ ≤ Real.exp (paperOpG a * paperOpU a) * Real.exp (paperOpG a * paperOpU a) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact (Real.log_le_log (by positivity) hbound).trans_eq (Real.log_exp _)

/-- ONE threshold gives the ACTUAL deterministic future budget simultaneously
for every operation; it is independent of every walk, base time and law. -/
theorem paperSchedule_uniform_future_shift (d : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ a ∈ paperScheduledOps d M g0,
      Real.log (paperFutureShift a + 1 : ℕ) ≤ 2 * (paperOpG a * paperOpU a) := by
  let C := max (3 * (2 / paperBandLogStep g0 + 1) + 1) 20
  have hratio := (tendsto_paperSchedule_weight_over_Xpow d 2 hd).eventually_ge_atTop C
  have hsmall := tendsto_paperScheduleMiddleG_zero.eventually (gt_mem_nhds hg0)
  apply Eventually.exists_forall_of_atTop
  filter_upwards [hratio, hsmall, paperSchedule_eventually_band_gap d hd,
    eventually_ge_atTop (1 : ℕ)] with M hratio hsmall hgap hM
  intro a ha
  have hga := paperBandG_bounds M g0 hM hg0 hsmall.le a.2.1
  have hU := paperOp_minU a ha hd hga.1 (hga.2.2.trans_lt hg01)
  have hW : paperScheduleMinG M * paperScheduleMinU d M ≤ paperOpG a * paperOpU a :=
    mul_le_mul hga.2.1 hU (Real.exp_pos _).le hga.1.le
  have hX := paperScheduleX_ge_count d M hd
  have hX1 : 1 ≤ paperScheduleX d M := by
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hgrowth : C * paperScheduleX d M ^ 2 ≤ paperScheduleMinG M * paperScheduleMinU d M :=
    (le_div_iff₀ (sq_pos_of_pos (paperScheduleX_pos d M hd))).mp hratio
  have h20 : 20 * paperScheduleX d M ≤ paperOpG a * paperOpU a := by
    have hC : 20 ≤ C := le_max_right _ _
    have h := mul_le_mul_of_nonneg_right hC (sq_nonneg (paperScheduleX d M))
    nlinarith
  have hcard : ((paperScheduledOps d M g0).card : ℝ) + 1 ≤ paperOpG a * paperOpU a := by
    have hc := paperScheduledOps_card_real_bound d M hd g0 hg0 hg01 hM hsmall.le
    have hC : 3 * (2 / paperBandLogStep g0 + 1) + 1 ≤ C := le_max_left _ _
    exact hc.trans ((mul_le_mul_of_nonneg_right hC (sq_nonneg _)).trans (hgrowth.trans hW))
  apply paperFutureShift_log_bound a
  · intro b hb
    exact paperOp_future_weight_le a b ha hd hM hg0 hg01 hsmall.le hgap (Finset.mem_filter.mp hb).2
  · exact (paperTerminalLength_le_exp d M hd).trans (Real.exp_le_exp.mpr h20)
  · have he : paperOpG a * paperOpU a ≤ Real.exp (paperOpG a * paperOpU a) := by
      linarith [Real.add_one_le_exp (paperOpG a * paperOpU a)]
    exact hcard.trans he

theorem paperFutureShift_displacement_log_bound {d M : ℕ} {g0 : ℝ}
    (a : PaperScheduleOp d M g0) (R : ℕ)
    (hlog : Real.log (paperFutureShift a + 1 : ℕ) ≤ 2 * (paperOpG a * paperOpU a)) :
    2 * Real.log (2 * ((R + 1) * paperFutureShift a) + 1 : ℕ) ≤
      4 * (paperOpG a * paperOpU a) + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  have h := displacement_log_bound (R + 1) (paperFutureShift a)
  linarith

/-- The actual ceiling offset at T_max gives its T_max^(-9) smoothing error
for every earlier source law and exact start. -/
theorem paper_terminal_smoothing_event_bound {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b : Ω → ℕ) (E : Set ℕ) (a d M : ℕ) (ha : (a : ℝ) ≤ paperScheduleMaxT d M) :
    |(smoothedTimeLaw μ b (terminalSmoothingLength (paperScheduleMaxT d M))).real
        ((fun t => t + a) ⁻¹' E) -
      (smoothedTimeLaw μ b (terminalSmoothingLength (paperScheduleMaxT d M))).real E| ≤
        1 / paperScheduleMaxT d M ^ 9 :=
  smoothedTimeLaw_ceiling_source_bound μ b E a _ (Real.exp_pos _) ha

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperSchedule_weight_over_Xpow
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLength_le_exp
#print axioms BinaryFormMoat.GeometryIntegration.paperFutureShift
#print axioms BinaryFormMoat.GeometryIntegration.paperFutureShift_log_bound
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_future_shift
#print axioms BinaryFormMoat.GeometryIntegration.paperFutureShift_displacement_log_bound
#print axioms BinaryFormMoat.GeometryIntegration.paper_terminal_smoothing_event_bound
