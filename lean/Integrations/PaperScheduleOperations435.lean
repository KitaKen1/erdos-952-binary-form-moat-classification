import Integrations.PaperScheduleBands435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- Every transition has a window, a band and a within-band ordinal. -/
abbrev PaperScheduleOp (d M : ℕ) (g0 : ℝ) :=
  Σ m : Fin (M + 1), Σ b : Fin 3, Fin (paperBandOperationCount d M m.val g0 b)

def paperScheduledOps (d M : ℕ) (g0 : ℝ) : Finset (PaperScheduleOp d M g0) :=
  Finset.univ.filter (fun o => (M + 1) / 2 ≤ o.1.val)

def paperOpG {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0) : ℝ :=
  paperBandG M g0 o.2.1

def paperOpU {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0) : ℝ :=
  paperBandScale (Real.exp (paperBandHi d o.1.val o.2.1)) (paperOpG o) o.2.2.val

theorem paperOp_log_bounds {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0)
    (hd : 1 ≤ d) (hg : 0 < paperOpG o) (hg1 : paperOpG o < 1) :
    paperBandLo d o.1.val o.2.1 ≤ Real.log (paperOpU o) ∧
      Real.log (paperOpU o) ≤ paperBandHi d o.1.val o.2.1 :=
  paperBandScale_mem_band _ _ _ (paperBand_bounds d o.1.val hd o.2.1).2.1
    hg hg1 o.2.2.val o.2.2.isLt

theorem paperOp_pos {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0)
    (hg : 0 < paperOpG o) : 0 < paperOpU o :=
  paperBandScale_pos _ _ (Real.exp_pos _) hg _

theorem paperOp_minU {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0)
    (ho : o ∈ paperScheduledOps d M g0) (hd : 1 ≤ d)
    (hg : 0 < paperOpG o) (hg1 : paperOpG o < 1) :
    paperScheduleMinU d M ≤ paperOpU o := by
  have hm : (M + 1) / 2 ≤ o.1.val := (Finset.mem_filter.mp ho).2
  exact paperScheduleMinU_le_stage d M o.1.val hd hm _ (paperOp_pos o hg)
    ((paperBand_bounds d o.1.val hd o.2.1).1.trans (paperOp_log_bounds o hd hg hg1).1)

/-- Actual finite operation data fill the former semantic scale/window fields.
The batch's T and mean L are still supplied by its prime batch. -/
def paperOpStage {d M : ℕ} {g0 : ℝ} (o : PaperScheduleOp d M g0)
    (ho : o ∈ paperScheduledOps d M g0) (hd : 1 ≤ d)
    (hg : 0 < paperOpG o) (hg1 : paperOpG o < 1)
    (T L : ℝ) (hT : 1 < T)
    (hlog : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d o.1.val)
    (hL : L ≤ 2 * Real.log T) : PaperScheduleStage d M g0 where
  window := o.1.val
  U := paperOpU o
  g := paperOpG o
  L := L
  T := T
  window_lower := (Finset.mem_filter.mp ho).2
  window_upper := by omega
  U_pos := paperOp_pos o hg
  T_gt_one := hT
  logU_lower := (paperBand_bounds d o.1.val hd o.2.1).1.trans
    (paperOp_log_bounds o hd hg hg1).1
  logT_upper := hlog
  mean_upper := hL
  slack_choice := by
    rcases o with ⟨m, b, n⟩
    fin_cases b <;> simp [paperOpG, paperBandG]

theorem paperScheduledOps_card_le (d M : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) (hM : 1 ≤ M)
    (hsmall : paperScheduleMiddleG M ≤ g0) :
    (paperScheduledOps d M g0).card ≤ 3 * (M + 1) * paperOperationCap d M g0 := by
  calc
    _ ≤ (Finset.univ : Finset (PaperScheduleOp d M g0)).card := Finset.card_filter_le _ _
    _ = ∑ m : Fin (M + 1), ∑ b : Fin 3, paperBandOperationCount d M m.val g0 b := by
      simp only [Finset.card_univ, Fintype.card_sigma, Fintype.card_fin]
    _ ≤ ∑ _m : Fin (M + 1), ∑ _b : Fin 3, paperOperationCap d M g0 := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro b _
      exact paperBandOperationCount_le_cap d M m.val hd (by omega) g0 hg0 hg01 hM hsmall b
    _ = _ := by simp; ring

/-- A coarse quadratic-in-X envelope is enough; no optimal operation count is needed. -/
theorem paperScheduledOps_card_real_bound (d M : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) (hM : 1 ≤ M)
    (hsmall : paperScheduleMiddleG M ≤ g0) :
    ((paperScheduledOps d M g0).card : ℝ) + 1 ≤
      (3 * (2 / paperBandLogStep g0 + 1) + 1) * paperScheduleX d M ^ 2 := by
  have hc : ((paperScheduledOps d M g0).card : ℝ) ≤
      3 * ((M : ℝ) + 1) * (paperOperationCap d M g0 : ℝ) := by
    exact_mod_cast paperScheduledOps_card_le d M hd g0 hg0 hg01 hM hsmall
  have hx := paperScheduleX_ge_count d M hd
  have hx1 : 1 ≤ paperScheduleX d M := by
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hs := paperBandLogStep_pos g0 hg0 hg01
  have hcap := paperOperationCap_real_bound d M hd g0 hg0 hg01
  have hcap' : (paperOperationCap d M g0 : ℝ) ≤
      (2 / paperBandLogStep g0 + 1) * paperScheduleX d M := by
    rw [div_eq_mul_inv] at hcap ⊢
    nlinarith
  have hp : 3 * ((M : ℝ) + 1) * (paperOperationCap d M g0 : ℝ) ≤
      3 * paperScheduleX d M * ((2 / paperBandLogStep g0 + 1) * paperScheduleX d M) := by
    gcongr
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.PaperScheduleOp
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduledOps
#print axioms BinaryFormMoat.GeometryIntegration.paperOpG
#print axioms BinaryFormMoat.GeometryIntegration.paperOpU
#print axioms BinaryFormMoat.GeometryIntegration.paperOp_log_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperOp_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperOp_minU
#print axioms BinaryFormMoat.GeometryIntegration.paperOpStage
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduledOps_card_le
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduledOps_card_real_bound
