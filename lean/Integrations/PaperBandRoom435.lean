import Integrations.PaperBandEntry435
import Integrations.PaperScheduleBands435

noncomputable section
open scoped Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter

/-- One numerical threshold covers any fixed polynomial margin and every
selected window, without interchanging limits over growing finite families. -/
theorem paperSchedule_polynomial_room (d : ℕ) (hd : 1 ≤ d) (c C : ℝ)
    (hc : 0 < c) (n : ℕ) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      C * (M : ℝ) ^ n ≤ c * paperScheduleX d m := by
  let a := Real.log (paperScheduleBase d) / 2
  have ha : 0 < a := div_pos (Real.log_pos (paperScheduleBase_gt_one d hd)) (by norm_num)
  have hgap := ((tendsto_exponential_polynomial_gap a c C 0 n ha hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
  apply Eventually.exists_forall_of_atTop
  filter_upwards [hgap] with M hM
  intro m hm
  have hx := (paperScheduleX_half_lower d M hd).trans (paperScheduleX_mono d hd hm)
  have hcx := mul_le_mul_of_nonneg_left hx hc.le
  dsimp [Function.comp_def, a] at hM hcx
  linarith

def paperMiddleIterations (M : ℕ) : ℕ := M ^ 3
def paperBottomIterations (M : ℕ) : ℕ := 200 * M ^ 20

theorem paperScheduleMiddle_logStep (M : ℕ) :
    paperBandLogStep (paperScheduleMiddleG M) = 2 * (M : ℝ) ^ 3 := by
  unfold paperScheduleMiddleG
  rw [paperBandLogStep_eq_neg_log _ (Real.exp_pos _)]
  rw [Real.log_exp]
  ring

theorem paperScheduleBottom_logStep (M : ℕ) :
    paperBandLogStep (paperScheduleMinG M) = 200 * (M : ℝ) ^ 20 := by
  unfold paperScheduleMinG
  rw [paperBandLogStep_eq_neg_log _ (Real.exp_pos _)]
  rw [Real.log_exp]
  ring

/-- The actual M^3 middle-band transitions and their recording scale fit. -/
theorem paperSchedule_middle_iterations_fit (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ((paperMiddleIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMiddleG M) ≤
        paperBandHi d m 1 - paperBandLo d m 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (1 / (10 * d)) 4 (by positivity) 6
  refine ⟨max M0 1, ?_⟩
  intro M hM m hm
  have hs := hM0 M ((le_max_left _ _).trans hM) m hm
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right M0 1).trans hM
  have hp : 1 ≤ (M : ℝ) ^ 3 := one_le_pow₀ hM1
  have he : ((M : ℝ) ^ 3) ^ 2 = (M : ℝ) ^ 6 := by ring
  have hwidth : paperBandHi d m 1 - paperBandLo d m 1 =
      (1 / (10 * (d : ℝ))) * paperScheduleX d m := by
    norm_num [paperBandHi, paperBandLo, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hwidth, paperScheduleMiddle_logStep]
  simp only [paperMiddleIterations, Nat.cast_pow]
  nlinarith

/-- The actual 200M^20 bottom-band transitions and recording scale fit. -/
theorem paperSchedule_bottom_iterations_fit (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ((paperBottomIterations M : ℝ) + 1) * paperBandLogStep (paperScheduleMinG M) ≤
        paperBandHi d m 2 - paperBandLo d m 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (1 / (20 * d)) 40200 (by positivity) 40
  refine ⟨max M0 1, ?_⟩
  intro M hM m hm
  have hs := hM0 M ((le_max_left _ _).trans hM) m hm
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right M0 1).trans hM
  have hp : 1 ≤ (M : ℝ) ^ 20 := one_le_pow₀ hM1
  have he : ((M : ℝ) ^ 20) ^ 2 = (M : ℝ) ^ 40 := by ring
  have hwidth : paperBandHi d m 2 - paperBandLo d m 2 =
      (1 / (20 * (d : ℝ))) * paperScheduleX d m := by
    norm_num [paperBandHi, paperBandLo, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hwidth, paperScheduleBottom_logStep]
  simp only [paperBottomIterations, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

/-- A batch starts at the first top-band scale <=a0*T. A fixed number of
transitions fits simultaneously for all selected batch windows and scales. -/
theorem paperSchedule_top_block_fits (d : ℕ) (hd : 1 ≤ d) (a0 g0 : ℝ)
    (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (hg0 : 0 < g0) (hg01 : g0 < 1) (l : ℕ) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ∀ T : ℕ, 2 ≤ T → paperScheduleX d m ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m →
        paperBandEntry (paperBandHi d m 0) g0 (a0 * T) + l <
          paperBandOperationCount d M m g0 0 := by
  obtain ⟨M0, hM0⟩ := paperSchedule_polynomial_room d hd (1 / 5)
    (((l : ℝ) + 1) * paperBandLogStep g0 - Real.log a0) (by norm_num) 0
  refine ⟨M0, ?_⟩
  intro M hM m hm T hT hlo hhi
  have hs := hM0 M hM m hm
  simp only [pow_zero, mul_one] at hs
  have hTP : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hV : Real.log (a0 * T) = Real.log a0 + Real.log (T : ℝ) :=
    Real.log_mul ha0.ne' hTP.ne'
  have ha : Real.log a0 ≤ 0 := Real.log_nonpos ha0.le ha01
  have hx := (paperScheduleX_pos d m hd).le
  have hvhi : Real.log (a0 * T) ≤ paperBandHi d m 0 := by
    rw [hV]
    simp only [paperBandHi, ↓reduceIte]
    linarith
  have hvlo : paperBandLo d m 0 + ((l : ℝ) + 1) * paperBandLogStep g0 ≤ Real.log (a0 * T) := by
    rw [hV]
    simp only [paperBandLo, ↓reduceIte]
    linarith
  simpa only [paperBandOperationCount, paperBandG, ↓reduceIte] using
    paperBandEntry_block_fits (paperBandLo d m 0) (paperBandHi d m 0) g0 (a0 * T)
      hg0 hg01 hvhi l hvlo


/-- Choose fixed accuracy constants before the asymptotic schedule. -/
theorem paperEnrichment_fixed_accuracy (ε : ℝ) (hε : 0 < ε) :
    ∃ l0 : ℕ, ∃ g0 : ℝ, 0 < g0 ∧ g0 < 1 / 64 ∧
      ∀ l ≥ l0, ∀ g : ℝ, 0 ≤ g → g ≤ g0 → 80 * g + (1 / 2 : ℝ) ^ l ≤ ε := by
  have hp : Tendsto (fun l : ℕ => (1 / 2 : ℝ) ^ l) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨l0, hl0⟩ := (hp.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists_forall_of_atTop
  refine ⟨l0, min (1 / 128) (ε / 160), lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro l hl g _ hg
  have hgε := hg.trans (min_le_right (1 / 128) (ε / 160))
  have hpow := hl0 l hl
  linarith

theorem paper_half_pow_exp (n : ℕ) :
    (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2 * n) := by
  calc
    _ = (Real.exp (-Real.log 2)) ^ n := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem paperMiddle_deficit_bound (M : ℕ) :
    80 * paperScheduleMiddleG M + (1 / 2 : ℝ) ^ paperMiddleIterations M ≤
      81 * Real.exp (-Real.log 2 * (M : ℝ) ^ 3) := by
  have hlog : Real.log 2 ≤ 1 := (by linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)] : _)
  have he : Real.exp (-(M : ℝ) ^ 3) ≤ Real.exp (-Real.log 2 * (M : ℝ) ^ 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [pow_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) 3]
  rw [paper_half_pow_exp]
  simp only [paperMiddleIterations, Nat.cast_pow, paperScheduleMiddleG]
  linarith

/-- The middle deficit is exponentially small in M^3 with explicit c=log(2)/2. -/
theorem paperMiddle_deficit_eventually :
    ∃ M0 : ℕ, ∀ M ≥ M0,
      80 * paperScheduleMiddleG M + (1 / 2 : ℝ) ^ paperMiddleIterations M ≤
        Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) := by
  have hc : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht : Tendsto (fun M : ℕ => (Real.log 2 / 2) * (M : ℝ) ^ 3) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply Eventually.exists_forall_of_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.log 81)] with M hM
  have he : 81 ≤ Real.exp ((Real.log 2 / 2) * (M : ℝ) ^ 3) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 81)] using Real.exp_le_exp.mpr hM
  apply (paperMiddle_deficit_bound M).trans
  calc
    _ ≤ Real.exp ((Real.log 2 / 2) * (M : ℝ) ^ 3) * Real.exp (-Real.log 2 * (M : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The paper's 200M^20 iterations supply its exp(-90M^20) local accuracy. -/
theorem paperBottom_deficit_bound (M : ℕ) (hM : 1 ≤ M) :
    80 * paperScheduleMinG M + (1 / 2 : ℝ) ^ paperBottomIterations M ≤
      Real.exp (-90 * (M : ℝ) ^ 20) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hx : 1 ≤ (M : ℝ) ^ 20 := one_le_pow₀ (by exact_mod_cast hM)
  have hp : (1 / 2 : ℝ) ^ paperBottomIterations M ≤ Real.exp (-100 * (M : ℝ) ^ 20) := by
    rw [paper_half_pow_exp]
    simp only [paperBottomIterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    apply Real.exp_le_exp.mpr
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbig : (81 : ℝ) ≤ Real.exp 10 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 10
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hmargin : (81 : ℝ) ≤ Real.exp (10 * (M : ℝ) ^ 20) :=
    hbig.trans (Real.exp_le_exp.mpr (by linarith))
  calc
    _ ≤ 81 * Real.exp (-100 * (M : ℝ) ^ 20) := by unfold paperScheduleMinG; linarith
    _ ≤ Real.exp (10 * (M : ℝ) ^ 20) * Real.exp (-100 * (M : ℝ) ^ 20) :=
      mul_le_mul_of_nonneg_right hmargin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_polynomial_room
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleIterations
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomIterations
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMiddle_logStep
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleBottom_logStep
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_middle_iterations_fit
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_bottom_iterations_fit
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_top_block_fits

#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichment_fixed_accuracy
#print axioms BinaryFormMoat.GeometryIntegration.paper_half_pow_exp
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_deficit_bound
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_deficit_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperBottom_deficit_bound
