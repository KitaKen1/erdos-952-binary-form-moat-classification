import Integrations.PaperCheckpointScales435
import Integrations.PaperScheduleBlocks435
import Integrations.PaperTailHistory435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- An ACTUAL middle-band operation in the common sorted schedule. -/
def paperMiddleCheckpointOp {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1)) (T : ℝ) (i : ℕ)
    (hfit : paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
      (paperCheckpointTarget d T i) < paperBandOperationCount d M m.val g0 1) :
    PaperScheduleOp d M g0 :=
  ⟨m, 1, ⟨paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
    (paperCheckpointTarget d T i), hfit⟩⟩

theorem paperMiddleCheckpointOp_mem {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (T : ℝ) (i : ℕ) (hfit) :
    paperMiddleCheckpointOp (d := d) g0 m T i hfit ∈ paperScheduledOps d M g0 := by
  simpa only [paperScheduledOps, paperMiddleCheckpointOp, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem paperMiddleCheckpointOp_g {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (T : ℝ) (i : ℕ) (hfit) :
    paperOpG (paperMiddleCheckpointOp (d := d) g0 m T i hfit) = paperScheduleMiddleG M := by
  simp [paperOpG, paperMiddleCheckpointOp, paperBandG]

theorem paperMiddleCheckpointOp_scale_bounds {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (T : ℝ) (i : ℕ) (hfit) (hg1 : paperScheduleMiddleG M < 1)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m.val 1) :
    (paperScheduleMiddleG M) ^ 2 * paperCheckpointTarget d T i <
      paperOpU (paperMiddleCheckpointOp (d := d) g0 m T i hfit) ∧
      paperOpU (paperMiddleCheckpointOp (d := d) g0 m T i hfit) ≤ paperCheckpointTarget d T i := by
  have h := paperBandEntry_scale_bounds (paperBandHi d m.val 1) (paperScheduleMiddleG M)
    (paperCheckpointTarget d T i) (Real.exp_pos _) hg1 (paperCheckpointTarget_pos d T i) hhi
  unfold paperOpU
  rw [paperMiddleCheckpointOp_g]
  simpa only [paperMiddleCheckpointOp] using h

/-- Every preceding ordinal has scale STRICTLY above the target; this also
handles the n=0 boundary without assuming the target is a grid value. -/
theorem paperBandEntry_before_scale (hi g V : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (n : ℕ) (hn : n < paperBandEntry hi g V) :
    V < paperBandScale (Real.exp hi) g n := by
  have hs := paperBandLogStep_pos g hg hg1
  have hr : (n : ℝ) < (hi - Real.log V) / paperBandLogStep g := Nat.lt_ceil.mp hn
  have hmul := (lt_div_iff₀ hs).mp hr
  have hu := paperBandScale_pos (Real.exp hi) g (Real.exp_pos _) hg n
  have he : Real.log (paperBandScale (Real.exp hi) g n) = hi - (n : ℝ) * paperBandLogStep g := by
    rw [paperBandScale_log _ _ (Real.exp_pos _) hg, Real.log_exp,
      paperBandLogStep_eq_neg_log g hg]
    ring
  have hlog : Real.log V < Real.log (paperBandScale (Real.exp hi) g n) := by rw [he]; linarith
  by_cases hv : 0 < V
  · exact (Real.log_lt_log_iff hv hu).mp hlog
  · exact lt_of_le_of_lt (by linarith) hu

/-- The constructed operation is genuinely the FIRST global operation with
scale <=target, not merely the first one in a separately restarted band. -/
theorem paperMiddleCheckpointOp_first {d M : ℕ} (hd : 1 ≤ d) (g0 : ℝ)
    (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (T : ℝ) (i : ℕ)
    (hfit : paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
      (paperCheckpointTarget d T i) < paperBandOperationCount d M m.val g0 1)
    (hG : ∀ o : PaperScheduleOp d M g0, 0 < paperOpG o ∧ paperOpG o < 1)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m.val 1)
    (a : PaperScheduleOp d M g0) (ha : a ∈ paperScheduledOps d M g0)
    (hpos : paperOpPosition a < paperOpPosition (paperMiddleCheckpointOp g0 m T i hfit)) :
    paperCheckpointTarget d T i < paperOpU a := by
  have hmem := paperMiddleCheckpointOp_mem g0 m hm T i hfit
  have horder := (paperOpPosition_le_iff a _ ha hmem).mp hpos.le
  have hla := (paperOp_log_bounds a hd (hG a).1 (hG a).2).1
  have hU := paperOp_pos a (hG a).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold paperOpLater at horder
  dsimp [paperMiddleCheckpointOp] at horder
  rcases horder with hw | ⟨hw, hb⟩ | ⟨hw, hb, hn⟩
  · have hg := paperBand_next_window_gap d a.1.val m.val hd hw a.2.1 1
    have hp : 0 < paperScheduleX d a.1.val / (100 * d) := by
      exact div_pos (paperScheduleX_pos d a.1.val hd) (by positivity)
    apply (Real.log_lt_log_iff (paperCheckpointTarget_pos d T i) hU).mp
    linarith
  · have hg := paperBand_same_window_gap d m.val hd a.2.1 1 hb
    conv at hla => lhs; arg 2; rw [← hw]
    have hp : 0 < paperScheduleX d m.val / (100 * d) := by
      exact div_pos (paperScheduleX_pos d m.val hd) (by positivity)
    apply (Real.log_lt_log_iff (paperCheckpointTarget_pos d T i) hU).mp
    linarith
  · rcases a with ⟨ma, ba, na⟩
    have hmw : ma = m := Fin.ext hw.symm
    subst ma
    have hbw : ba = 1 := Fin.ext hb.symm
    subst ba
    have hne : na.val ≠ paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
        (paperCheckpointTarget d T i) := by
      intro he
      have he' : na = ⟨paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
        (paperCheckpointTarget d T i), hfit⟩ := Fin.ext he
      subst na
      dsimp [paperMiddleCheckpointOp] at hpos
      omega
    dsimp only at hn
    have hn' : na.val < paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
        (paperCheckpointTarget d T i) := by omega
    have hgm : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
    have hg1 : paperScheduleMiddleG M < 1 := by
      simpa only [paperOpG, hgm] using (hG (⟨m, 1, na⟩ : PaperScheduleOp d M g0)).2
    simpa only [paperOpU, paperOpG, hgm] using
      paperBandEntry_before_scale (paperBandHi d m.val 1) (paperScheduleMiddleG M)
        (paperCheckpointTarget d T i) (show 0 < paperScheduleMiddleG M from Real.exp_pos _)
        hg1 na.val hn'

theorem paperOpPosition_band_strict {d M : ℕ} {g0 : ℝ} (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (b : Fin 3) (n q : ℕ)
    (hn : n < paperBandOperationCount d M m.val g0 b)
    (hq : q < paperBandOperationCount d M m.val g0 b) (hlt : n < q) :
    paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, hn⟩⟩ <
      paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨q, hq⟩⟩ := by
  have mem (j : Fin (paperBandOperationCount d M m.val g0 b)) :
      (⟨m, b, j⟩ : PaperScheduleOp d M g0) ∈ paperScheduledOps d M g0 := by
    simpa only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have hl := (paperOpPosition_le_iff _ _ (mem ⟨n, hn⟩) (mem ⟨q, hq⟩)).mpr
    (by unfold paperOpLater; dsimp; omega)
  have hne : paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, hn⟩⟩ ≠
      paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨q, hq⟩⟩ := by
    intro he
    have hi : (⟨paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, hn⟩⟩,
        paperOpPosition_lt _ (mem ⟨n, hn⟩)⟩ : Fin (paperScheduleList d M g0).length) =
      ⟨paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨q, hq⟩⟩,
        paperOpPosition_lt _ (mem ⟨q, hq⟩)⟩ := Fin.ext he
    have hv := congrArg (fun j => ((paperScheduleList d M g0).get j).2.2.val) hi
    rw [paperOpPosition_get _ (mem ⟨n, hn⟩), paperOpPosition_get _ (mem ⟨q, hq⟩)] at hv
    dsimp at hv
    omega
  omega

/-- The recording point after M^3 REAL transitions is strictly before the
next checkpoint in the ORIGINAL sorted schedule. -/
theorem paperMiddleCheckpoint_record_before_next {d M : ℕ} (hd : 1 ≤ d) (g0 : ℝ)
    (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (T : ℝ) (hM : 2 ≤ M) (i : ℕ)
    (hi : i < paperCheckpointStop d M T (by omega))
    (hfit : paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
      (paperCheckpointTarget d T i) + paperMiddleIterations M < paperBandOperationCount d M m.val g0 1)
    (hnext : paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M)
      (paperCheckpointTarget d T (i + 1)) < paperBandOperationCount d M m.val g0 1)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m.val 1) :
    paperOpPosition (paperMiddleCheckpointOp (d := d) g0 m T i (by omega)) + paperMiddleIterations M <
      paperOpPosition (paperMiddleCheckpointOp (d := d) g0 m T (i + 1) hnext) := by
  have hg := paperCheckpoint_middle_entry_gap d M m.val hd T hM i hi hhi
  have hp := paperOpPosition_band_strict m hm 1 _ _ hfit hnext hg
  rw [paperOpPosition_block m hm 1 _ (paperMiddleIterations M) hfit] at hp
  exact hp

/-- Recorded scale loses at most 4M^6 in its logarithm, with the ceiling step
included. This lower bound is independent of the exact starting time. -/
theorem paperCheckpoint_middle_record_log (d M m : ℕ) (T : ℝ) (i : ℕ) (hM : 1 ≤ M)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m 1)
    (hg1 : paperScheduleMiddleG M < 1) :
    paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6 <
      Real.log (paperBandScale (Real.exp (paperBandHi d m 1)) (paperScheduleMiddleG M)
        (paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
          paperMiddleIterations M)) := by
  have hg : 0 < paperScheduleMiddleG M := Real.exp_pos _
  have hb := (paperBandEntry_log_bounds (paperBandHi d m 1) (paperScheduleMiddleG M)
    (paperCheckpointTarget d T i) hg hg1 hhi).1
  have hs := paperMiddle_iteration_span_le M hM
  have eqlog (n : ℕ) : Real.log (paperBandScale (Real.exp (paperBandHi d m 1))
      (paperScheduleMiddleG M) n) = paperBandHi d m 1 - (n : ℝ) * paperBandLogStep (paperScheduleMiddleG M) := by
    rw [paperBandScale_log _ _ (Real.exp_pos _) hg, Real.log_exp,
      paperBandLogStep_eq_neg_log _ hg]
    ring
  rw [eqlog, paperCheckpointTarget_log] at hb
  rw [eqlog]
  push_cast
  nlinarith

/-- A constructed checkpoint's native displacement alphabet has log size
<=C_R*T^r. The bound is support-based and hence independent of the source law. -/
theorem paperMiddleCheckpoint_native_alphabet {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (T : ℝ) (i R : ℕ) (hfit) (hg1 : paperScheduleMiddleG M < 1)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m.val 1)
    (hV : 1 ≤ paperCheckpointTarget d T i)
    (hlog : Real.log (paperFutureShift (paperMiddleCheckpointOp (d := d) g0 m T i hfit) + 1 : ℕ) ≤
      2 * (paperOpG (paperMiddleCheckpointOp g0 m T i hfit) *
        paperOpU (paperMiddleCheckpointOp g0 m T i hfit))) :
    2 * Real.log (2 * ((R + 1) * paperFutureShift (paperMiddleCheckpointOp g0 m T i hfit)) + 1 : ℕ) ≤
      (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) * paperCheckpointTarget d T i := by
  have hc := paperFutureShift_displacement_log_bound (paperMiddleCheckpointOp g0 m T i hfit) R hlog
  have hu := (paperMiddleCheckpointOp_scale_bounds g0 m T i hfit hg1 hhi).2
  have hU := paperOp_pos (paperMiddleCheckpointOp g0 m T i hfit)
    (by rw [paperMiddleCheckpointOp_g]; exact Real.exp_pos _)
  have hmult := mul_le_mul_of_nonneg_right hg1.le hU.le
  have hconst : 0 ≤ 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * (R + 1) + 1)
  rw [paperMiddleCheckpointOp_g] at hc
  nlinarith [mul_le_mul_of_nonneg_left hV hconst]

/-- Integer recording retains half of the explicit exponential mass. -/
theorem paperCheckpoint_middle_record_rank_mass (d M m : ℕ) (T : ℝ) (i : ℕ) (hM : 1 ≤ M)
    (hhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m 1)
    (hg1 : paperScheduleMiddleG M < 1) (L : ℝ) (hL : 0 < L)
    (hsmall : L ≤ Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2) :
    Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤
      (paperInputRank
        (paperBandScale (Real.exp (paperBandHi d m 1)) (paperScheduleMiddleG M)
          (paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
            paperMiddleIterations M)) L : ℝ) * L := by
  have hg : 0 < paperScheduleMiddleG M := Real.exp_pos _
  have hU := paperBandScale_pos (Real.exp (paperBandHi d m 1)) (paperScheduleMiddleG M)
    (Real.exp_pos _) hg
    (paperBandEntry (paperBandHi d m 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
      paperMiddleIterations M)
  have hb := paperCheckpoint_middle_record_log d M m T i hM hhi hg1
  have he := Real.exp_lt_exp.mpr hb
  rw [Real.exp_log hU] at he
  have hf := (floorRank_log_bounds _ L hU.le hL).2
  change _ ≤ (⌊_ / L⌋₊ : ℝ) * L
  linarith

/-- Actual checkpoint witnesses for ALL indices at ONE threshold, with all
operations selected before the finite source, walk, starting law and labels. -/
theorem paperCheckpoint_uniform_schedule (d : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℝ,
      paperScheduleX d m.val ≤ Real.log T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m.val → ∀ i : ℕ,
        ∃ o : PaperScheduleOp d M g0,
          o ∈ paperScheduledOps d M g0 ∧ o.1 = m ∧ o.2.1 = 1 ∧
          (paperScheduleMiddleG M) ^ 2 * paperCheckpointTarget d T i < paperOpU o ∧
          paperOpU o ≤ paperCheckpointTarget d T i ∧
          paperOpPosition o + paperMiddleIterations M < (paperScheduleList d M g0).length ∧
          ∀ a : PaperScheduleOp d M g0, a ∈ paperScheduledOps d M g0 →
            paperOpPosition a < paperOpPosition o → paperCheckpointTarget d T i < paperOpU a := by
  obtain ⟨Mfit, hfit⟩ := paperCheckpoint_uniform_middle_blocks d hd
  obtain ⟨Msmall, hsmall⟩ := (tendsto_paperScheduleMiddleG_zero.eventually (gt_mem_nhds hg0)).exists_forall_of_atTop
  refine ⟨max (max Mfit Msmall) 1, ?_⟩
  intro M hM m hm T hlo hhi i
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMfit : Mfit ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hM)
  have hMsmall : Msmall ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
  have hG (o : PaperScheduleOp d M g0) : 0 < paperOpG o ∧ paperOpG o < 1 := by
    have h := paperBandG_bounds M g0 hM1 hg0 (hsmall M hMsmall).le o.2.1
    exact ⟨h.1, h.2.2.trans_lt hg01⟩
  have hf := hfit M hMfit m.val hm T g0 hlo hhi i
  let o := paperMiddleCheckpointOp (d := d) g0 m T i (by omega)
  have hom := paperMiddleCheckpointOp_mem (d := d) g0 m hm T i (by omega)
  have hg1 : paperScheduleMiddleG M < 1 := by
    simpa only [o, paperMiddleCheckpointOp_g] using (hG o).2
  have ht := (paperCheckpointTarget_log_bounds d m.val hd T hlo hhi i).2
  have hvhi : Real.log (paperCheckpointTarget d T i) ≤ paperBandHi d m.val 1 := by
    norm_num [paperBandHi, div_eq_mul_inv] at ht ⊢
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    nlinarith [mul_pos (paperScheduleX_pos d m.val hd) (inv_pos.mpr hdR)]
  have hu := paperMiddleCheckpointOp_scale_bounds g0 m T i (by omega) hg1 hvhi
  let nr := paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) +
    paperMiddleIterations M
  have hrm : (⟨m, 1, ⟨nr, hf⟩⟩ : PaperScheduleOp d M g0) ∈ paperScheduledOps d M g0 := by
    simpa only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have hrl := paperOpPosition_lt (⟨m, 1, ⟨nr, hf⟩⟩ : PaperScheduleOp d M g0) hrm
  have hblock := paperOpPosition_block m hm 1
    (paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i))
    (paperMiddleIterations M) hf
  rw [hblock] at hrl
  refine ⟨o, hom, rfl, rfl, hu.1, hu.2, hrl, ?_⟩
  exact paperMiddleCheckpointOp_first hd g0 m hm T i (by omega) hG hvhi

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpointOp
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpointOp_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpointOp_g
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpointOp_scale_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_before_scale
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpointOp_first
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_band_strict
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpoint_record_before_next
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_middle_record_log
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpoint_native_alphabet

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_middle_record_rank_mass
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_uniform_schedule
