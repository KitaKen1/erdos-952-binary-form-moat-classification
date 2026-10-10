import Integrations.ExponentialScheduleGrowth435
import Integrations.PaperScheduleScales435

noncomputable section
open scoped Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter

theorem paperScheduleMinG_pow (M C : ℕ) :
    paperScheduleMinG M ^ C = Real.exp (-(100 * C) * (M : ℝ) ^ 20) := by
  unfold paperScheduleMinG
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem tendsto_paperScheduleMinG_zero : Tendsto paperScheduleMinG atTop (𝓝 0) := by
  have hp : Tendsto (fun M : ℕ => (M : ℝ) ^ 20) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 20 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun M : ℕ => -100 * (M : ℝ) ^ 20) atTop atBot :=
    hp.const_mul_atTop_of_neg (by norm_num)
  exact Real.tendsto_exp_atBot.comp hn

theorem tendsto_paperScheduleMiddleG_zero : Tendsto paperScheduleMiddleG atTop (𝓝 0) := by
  have hp : Tendsto (fun M : ℕ => (M : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun M : ℕ => -(M : ℝ) ^ 3) atTop atBot := by
    simpa only [neg_one_mul] using hp.const_mul_atTop_of_neg (by norm_num : (-1 : ℝ) < 0)
  exact Real.tendsto_exp_atBot.comp hn

theorem paperScheduleMinG_le_middle (M : ℕ) (hM : 1 ≤ M) :
    paperScheduleMinG M ≤ paperScheduleMiddleG M := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp := pow_le_pow_right₀ hMR (by norm_num : 3 ≤ 20)
  apply Real.exp_le_exp.mpr
  change -100 * (M : ℝ) ^ 20 ≤ -(M : ℝ) ^ 3
  nlinarith [pow_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) 20]

/-- The ACTUAL paper extrema satisfy every fixed natural-power enrichment regime.
The lower window is ceil(M/2); it is not replaced by a fixed finite family. -/
theorem tendsto_paperSchedule_extremal_regime (d C : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun M => paperScheduleMinG M ^ C * paperScheduleMinU d M /
      Real.log (paperScheduleMaxT d M)) atTop atTop := by
  let b := Real.log (paperScheduleBase d)
  let a := b / 2
  let c := 1 / (20 * (d : ℝ))
  have hb : 0 < b := Real.log_pos (paperScheduleBase_gt_one d hd)
  have ha : 0 < a := by dsimp [a]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr := ((tendsto_double_exponential_ratio a c (100 * C) b 20 ha hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop (by norm_num : (0 : ℝ) < 20 / 21)
  apply tendsto_atTop_mono _ hr
  intro M
  have hU : Real.exp (c * Real.exp (a * M)) ≤ paperScheduleMinU d M := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right (paperScheduleX_half_lower d M hd)
      (show (0 : ℝ) ≤ 20 * d by positivity)
    simpa [c, a, b, div_eq_mul_inv, mul_comm] using h
  have hlog : Real.log (paperScheduleMaxT d M) = (21 / 20 : ℝ) * paperScheduleX d M :=
    Real.log_exp _
  have hx := paperScheduleX_exp d M hd
  have hxpos := paperScheduleX_pos d M hd
  dsimp [Function.comp_def]
  rw [paperScheduleMinG_pow, hlog, hx]
  calc
    (20 / 21 : ℝ) * (Real.exp (-(100 * C) * (M : ℝ) ^ 20) *
        Real.exp (c * Real.exp (a * M)) / Real.exp (b * M)) =
        Real.exp (-(100 * C) * (M : ℝ) ^ 20) * Real.exp (c * Real.exp (a * M)) /
          ((21 / 20 : ℝ) * Real.exp (b * M)) := by ring
    _ ≤ _ := by gcongr

/-- Semantic bounds satisfied by each paper operation and batch. The actual
ordered list of operations is constructed separately. -/
structure PaperScheduleStage (d M : ℕ) (g0 : ℝ) where
  window : ℕ
  U : ℝ
  g : ℝ
  L : ℝ
  T : ℝ
  window_lower : (M + 1) / 2 ≤ window
  window_upper : window ≤ M
  U_pos : 0 < U
  T_gt_one : 1 < T
  logU_lower : paperScheduleX d window / (20 * d) ≤ Real.log U
  logT_upper : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d window
  mean_upper : L ≤ 2 * Real.log T
  slack_choice : g = g0 ∨ g = paperScheduleMiddleG M ∨ g = paperScheduleMinG M

theorem paperScheduleStage_extremal_bounds (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (g0 : ℝ) (hg0 : paperScheduleMinG M ≤ g0) (s : PaperScheduleStage d M g0) :
    paperScheduleMinG M ≤ s.g ∧ paperScheduleMinU d M ≤ s.U ∧
      s.L ≤ 2 * Real.log (paperScheduleMaxT d M) := by
  have hU := paperScheduleMinU_le_stage d M s.window hd s.window_lower s.U s.U_pos s.logU_lower
  have hT := paperScheduleMaxT_ge_stage d M s.window hd s.window_upper s.T
    ((by norm_num : (0 : ℝ) < 1).trans s.T_gt_one) s.logT_upper
  have hmean := s.mean_upper.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log ((by norm_num : (0 : ℝ) < 1).trans s.T_gt_one) hT) (by norm_num))
  refine ⟨?_, hU, hmean⟩
  rcases s.slack_choice with h | h | h
  · simpa [h] using hg0
  · simpa [h] using paperScheduleMinG_le_middle M hM
  · simp [h]

/-- ONE common M handles EVERY admissible stage, even with a growing number
of stages, and all walks. The degree is fixed before taking this threshold. -/
theorem paperSchedule_uniform_size_threshold (f : Polynomial ℤ) (D : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 : ℝ) (hg0 : 0 < g0) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ s : PaperScheduleStage f.natDegree M g0,
      paperEnrichmentSizeConstant f D * s.L ≤ s.g ^ 10 * s.U := by
  have hg := tendsto_paperScheduleMinG_zero.eventually (gt_mem_nhds hg0)
  have hs := paperEnrichmentSize_eventually atTop f D
    (paperScheduleMinU f.natDegree) paperScheduleMinG
    (fun M => 2 * Real.log (paperScheduleMaxT f.natDegree M))
    (paperScheduleMaxT f.natDegree)
    (Eventually.of_forall (fun M => by
      change 1 < Real.exp _
      exact Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (paperScheduleX_pos _ M hd))))
    (Eventually.of_forall (fun _ => le_rfl)) (tendsto_paperSchedule_extremal_regime _ 10 hd)
  apply Eventually.exists_forall_of_atTop
  filter_upwards [hs, hg, eventually_ge_atTop (1 : ℕ)] with M hsize hg0M hM
  intro s
  obtain ⟨hsg, hsU, hsL⟩ := paperScheduleStage_extremal_bounds _ M hd hM g0 hg0M.le s
  have hpos : 0 ≤ paperScheduleMinG M := (Real.exp_pos _).le
  have hpow := pow_le_pow_left₀ hpos hsg 10
  have hmul := mul_le_mul hpow hsU (Real.exp_pos _).le (pow_nonneg (hpos.trans hsg) 10)
  exact (mul_le_mul_of_nonneg_left hsL (paperEnrichmentSizeConstant_pos f D).le).trans
    (hsize.trans hmul)

/-- The same common threshold also supplies positivity and the small-slack
domain required by actual enrichment, for all three paper bands. -/
theorem paperSchedule_uniform_enrichment_threshold (f : Polynomial ℤ) (D : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ s : PaperScheduleStage f.natDegree M g0,
      0 < s.g ∧ s.g < 1 / 64 ∧ paperEnrichmentSizeConstant f D * s.L ≤ s.g ^ 10 * s.U := by
  obtain ⟨M0, hM0⟩ := paperSchedule_uniform_size_threshold f D hd g0 hg0
  have hmiddle := tendsto_paperScheduleMiddleG_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  apply Eventually.exists_forall_of_atTop
  filter_upwards [hmiddle, eventually_ge_atTop M0, eventually_ge_atTop (1 : ℕ)] with M hmid hM hM1
  intro s
  have hpos : 0 < s.g := by
    rcases s.slack_choice with h | h | h
    · simpa [h] using hg0
    · rw [h]; exact Real.exp_pos _
    · rw [h]; exact Real.exp_pos _
  refine ⟨hpos, ?_, hM0 M hM s⟩
  rcases s.slack_choice with h | h | h
  · simpa [h] using hg064
  · simpa [h] using hmid
  · simpa [h] using (paperScheduleMinG_le_middle M hM1).trans_lt hmid

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMinG_pow
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperScheduleMinG_zero
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperScheduleMiddleG_zero
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMinG_le_middle
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperSchedule_extremal_regime
#print axioms BinaryFormMoat.GeometryIntegration.PaperScheduleStage
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleStage_extremal_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_size_threshold
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_enrichment_threshold
