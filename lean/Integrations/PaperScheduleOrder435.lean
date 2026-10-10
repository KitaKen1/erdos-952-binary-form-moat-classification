import Integrations.PaperScheduleOperations435
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter

/-- Future operations: decreasing window, then increasing band, then ordinal.
Equality is included because the current transition belongs to its future shift. -/
def paperOpLater {d M : ℕ} {g0 : ℝ} (a b : PaperScheduleOp d M g0) : Prop :=
  b.1.val < a.1.val ∨
  (b.1.val = a.1.val ∧ a.2.1.val < b.2.1.val) ∨
  (b.1.val = a.1.val ∧ b.2.1.val = a.2.1.val ∧ a.2.2.val ≤ b.2.2.val)

theorem paperOpLater_refl {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0) :
    paperOpLater a a := by unfold paperOpLater; omega

theorem paperOpLater_trans {d M : ℕ} {g0 : ℝ} (a b c : PaperScheduleOp d M g0)
    (hab : paperOpLater a b) (hbc : paperOpLater b c) : paperOpLater a c := by
  unfold paperOpLater at *
  omega

theorem paperOpLater_total {d M : ℕ} {g0 : ℝ} (a b : PaperScheduleOp d M g0) :
    paperOpLater a b ∨ paperOpLater b a := by unfold paperOpLater; omega

theorem paperOpLater_antisymm {d M : ℕ} {g0 : ℝ} (a b : PaperScheduleOp d M g0)
    (hab : paperOpLater a b) (hba : paperOpLater b a) : a = b := by
  rcases a with ⟨ma, ba, na⟩
  rcases b with ⟨mb, bb, nb⟩
  unfold paperOpLater at hab hba
  have hw : ma = mb := Fin.ext (by dsimp at hab hba; omega)
  subst mb
  have hb : ba = bb := Fin.ext (by dsimp at hab hba; omega)
  subst bb
  have hn : na = nb := Fin.ext (by dsimp at hab hba; omega)
  subst nb
  rfl

instance paperOpLater_isTrans (d M : ℕ) (g0 : ℝ) :
    IsTrans (PaperScheduleOp d M g0) paperOpLater := ⟨paperOpLater_trans⟩

instance paperOpLater_isAntisymm (d M : ℕ) (g0 : ℝ) :
    Std.Antisymm (@paperOpLater d M g0) := ⟨paperOpLater_antisymm⟩

instance paperOpLater_isTotal (d M : ℕ) (g0 : ℝ) :
    Std.Total (@paperOpLater d M g0) := ⟨paperOpLater_total⟩

/-- The whole paper transition list, in decreasing-window/band/ordinal order. -/
def paperScheduleList (d M : ℕ) (g0 : ℝ) : List (PaperScheduleOp d M g0) :=
  (paperScheduledOps d M g0).sort paperOpLater

theorem paperScheduleList_mem {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0) :
    a ∈ paperScheduleList d M g0 ↔ a ∈ paperScheduledOps d M g0 := Finset.mem_sort _

theorem paperScheduleList_length (d M : ℕ) (g0 : ℝ) :
    (paperScheduleList d M g0).length = (paperScheduledOps d M g0).card := Finset.length_sort _

theorem paperScheduleList_pairwise (d M : ℕ) (g0 : ℝ) :
    (paperScheduleList d M g0).Pairwise paperOpLater := Finset.pairwise_sort _ _

theorem paperBand_same_window_gap (d m : ℕ) (hd : 1 ≤ d) (a b : Fin 3)
    (hab : a.val < b.val) :
    paperScheduleX d m / (100 * d) ≤ paperBandLo d m a - paperBandHi d m b := by
  have hx := (paperScheduleX_pos d m hd).le
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hy0 : 0 ≤ paperScheduleX d m / d := div_nonneg hx (by linarith)
  have hy1 : paperScheduleX d m / d ≤ paperScheduleX d m := div_le_self hx hdR
  simp only [div_eq_mul_inv] at hy0 hy1
  fin_cases a <;> fin_cases b <;> norm_num at hab <;>
    norm_num [paperBandLo, paperBandHi, div_eq_mul_inv] <;> nlinarith

theorem paperBand_next_window_gap (d m n : ℕ) (hd : 1 ≤ d) (hnm : n < m)
    (a b : Fin 3) :
    paperScheduleX d m / (100 * d) ≤ paperBandLo d m a - paperBandHi d n b := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx := paperScheduleX_pos d m hd
  have hnext := paperScheduleX_mono d hd (by omega : n + 1 ≤ m)
  rw [paperScheduleX_succ] at hnext
  have hxn : paperScheduleX d n ≤ paperScheduleX d m / (100 * d) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [paperScheduleBase, mul_comm] using hnext)
  have hlo := (paperBand_bounds d m hd a).1
  have hhi := (paperBand_bounds d n hd b).2.2
  norm_num [div_eq_mul_inv] at hxn hlo ⊢
  nlinarith [mul_nonneg hx.le (inv_nonneg.mpr hdR.le)]

/-- The small parameter ratio is absorbed by a coarse interband log gap. -/
theorem paperSchedule_eventually_band_gap (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ M : ℕ in atTop,
      100 * (M : ℝ) ^ 20 ≤ paperScheduleX d ((M + 1) / 2) / (100 * d) := by
  let a := Real.log (paperScheduleBase d) / 2
  have ha : 0 < a := by
    have h := Real.log_pos (paperScheduleBase_gt_one d hd)
    dsimp [a]
    positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h := (tendsto_exponential_polynomial_gap a (1 / (100 * d)) 100 0 20 ha
    (by positivity)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.eventually_ge_atTop 0] with M hM
  have hx := paperScheduleX_half_lower d M hd
  have hm := div_le_div_of_nonneg_right hx (show (0 : ℝ) ≤ 100 * d by positivity)
  dsimp [Function.comp_def, a] at hM
  simp only [zero_mul, sub_zero, div_eq_mul_inv] at hM hm ⊢
  nlinarith

/-- Ordered band/window data imply decreasing transition log-lengths.
The comparison includes the switch from a tiny-g bottom band to the next top. -/
theorem paperOp_future_weight_le {d M : ℕ} {g0 : ℝ}
    (a b : PaperScheduleOp d M g0) (ha : a ∈ paperScheduledOps d M g0)
    (hd : 1 ≤ d) (hM : 1 ≤ M) (hg0 : 0 < g0) (hg01 : g0 < 1)
    (hsmall : paperScheduleMiddleG M ≤ g0)
    (hgap : 100 * (M : ℝ) ^ 20 ≤ paperScheduleX d ((M + 1) / 2) / (100 * d))
    (hlater : paperOpLater a b) : paperOpG b * paperOpU b ≤ paperOpG a * paperOpU a := by
  have hga := paperBandG_bounds M g0 hM hg0 hsmall a.2.1
  have hgb := paperBandG_bounds M g0 hM hg0 hsmall b.2.1
  have hUa := paperOp_pos a hga.1
  have hUb := paperOp_pos b hgb.1
  have hla := paperOp_log_bounds a hd hga.1 (hga.2.2.trans_lt hg01)
  have hlb := paperOp_log_bounds b hd hgb.1 (hgb.2.2.trans_lt hg01)
  have hhalf : (M + 1) / 2 ≤ a.1.val := (Finset.mem_filter.mp ha).2
  have hX := div_le_div_of_nonneg_right (paperScheduleX_mono d hd hhalf)
    (show (0 : ℝ) ≤ 100 * d by positivity)
  have compare (hlog : 100 * (M : ℝ) ^ 20 ≤ Real.log (paperOpU a) - Real.log (paperOpU b)) :
      paperOpG b * paperOpU b ≤ paperOpG a * paperOpU a := by
    have hu : paperOpU b ≤ paperScheduleMinG M * paperOpU a := by
      conv_lhs => rw [← Real.exp_log hUb]
      conv_rhs => rw [← Real.exp_log hUa]
      unfold paperScheduleMinG
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ paperOpU b := mul_le_of_le_one_left hUb.le (hgb.2.2.trans hg01.le)
      _ ≤ paperScheduleMinG M * paperOpU a := hu
      _ ≤ _ := mul_le_mul_of_nonneg_right hga.2.1 hUa.le
  rcases hlater with hwin | ⟨hwin, hband⟩ | ⟨hwin, hband, hstep⟩
  · apply compare
    have h := paperBand_next_window_gap d a.1.val b.1.val hd hwin a.2.1 b.2.1
    linarith
  · apply compare
    have h := paperBand_same_window_gap d a.1.val hd a.2.1 b.2.1 hband
    have hlb' : Real.log (paperOpU b) ≤ paperBandHi d a.1.val b.2.1 := by
      simpa only [hwin] using hlb.2
    linarith
  · rcases a with ⟨ma, ba, na⟩
    rcases b with ⟨mb, bb, nb⟩
    have hw : mb = ma := Fin.ext hwin
    subst mb
    have hb : bb = ba := Fin.ext hband
    subst bb
    exact mul_le_mul_of_nonneg_left
      (paperBandScale_antitone _ _ (Real.exp_pos _).le hga.1.le
        (hga.2.2.trans hg01.le) hstep) hga.1.le

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_refl
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_trans
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_total
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_antisymm
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_isTrans
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_isAntisymm
#print axioms BinaryFormMoat.GeometryIntegration.paperOpLater_isTotal
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_length
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_pairwise
#print axioms BinaryFormMoat.GeometryIntegration.paperBand_same_window_gap
#print axioms BinaryFormMoat.GeometryIntegration.paperBand_next_window_gap
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_eventually_band_gap
#print axioms BinaryFormMoat.GeometryIntegration.paperOp_future_weight_le
