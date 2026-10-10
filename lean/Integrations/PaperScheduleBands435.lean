import Integrations.PaperBandIteration435
import Mathlib.Tactic.FinCases

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- Top, middle and bottom are numbered 0,1,2 in processing order. -/
def paperBandLo (d m : ℕ) (b : Fin 3) : ℝ :=
  if b = 0 then (4 / 5 : ℝ) * paperScheduleX d m
  else if b = 1 then paperScheduleX d m / (5 * d)
  else paperScheduleX d m / (20 * d)

def paperBandHi (d m : ℕ) (b : Fin 3) : ℝ :=
  if b = 0 then (13 / 10 : ℝ) * paperScheduleX d m
  else if b = 1 then 3 * paperScheduleX d m / (10 * d)
  else paperScheduleX d m / (10 * d)

def paperBandG (M : ℕ) (g0 : ℝ) (b : Fin 3) : ℝ :=
  if b = 0 then g0 else if b = 1 then paperScheduleMiddleG M else paperScheduleMinG M

def paperBandOperationCount (d M m : ℕ) (g0 : ℝ) (b : Fin 3) : ℕ :=
  paperBandLength (paperBandLo d m b) (paperBandHi d m b) (paperBandG M g0 b)

def paperOperationCap (d M : ℕ) (g0 : ℝ) : ℕ :=
  ⌊2 * paperScheduleX d M / paperBandLogStep g0⌋₊ + 1

theorem paperBand_bounds (d m : ℕ) (hd : 1 ≤ d) (b : Fin 3) :
    paperScheduleX d m / (20 * d) ≤ paperBandLo d m b ∧
    paperBandLo d m b ≤ paperBandHi d m b ∧
    paperBandHi d m b ≤ 2 * paperScheduleX d m := by
  have hx := (paperScheduleX_pos d m hd).le
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hy0 : 0 ≤ paperScheduleX d m / d := div_nonneg hx (by linarith)
  have hy1 : paperScheduleX d m / d ≤ paperScheduleX d m := div_le_self hx hdR
  simp only [div_eq_mul_inv] at hy0 hy1
  fin_cases b <;> norm_num [paperBandLo, paperBandHi, div_eq_mul_inv] <;>
    constructor <;> first | constructor <;> nlinarith | nlinarith

theorem paperBandG_bounds (M : ℕ) (g0 : ℝ) (hM : 1 ≤ M) (hg0 : 0 < g0)
    (hsmall : paperScheduleMiddleG M ≤ g0) (b : Fin 3) :
    0 < paperBandG M g0 b ∧ paperScheduleMinG M ≤ paperBandG M g0 b ∧
      paperBandG M g0 b ≤ g0 := by
  have hm := paperScheduleMinG_le_middle M hM
  have hmid : 0 < paperScheduleMiddleG M := Real.exp_pos _
  have hmin : 0 < paperScheduleMinG M := Real.exp_pos _
  fin_cases b <;> simp only [paperBandG] <;> constructor
  · exact hg0
  · exact ⟨hm.trans hsmall, le_rfl⟩
  · exact hmid
  · exact ⟨hm, hsmall⟩
  · exact hmin
  · exact ⟨le_rfl, hm.trans hsmall⟩

theorem paperBandOperationCount_le_cap (d M m : ℕ) (hd : 1 ≤ d) (hm : m ≤ M)
    (g0 : ℝ) (hg0 : 0 < g0) (hg01 : g0 < 1) (hM : 1 ≤ M)
    (hsmall : paperScheduleMiddleG M ≤ g0) (b : Fin 3) :
    paperBandOperationCount d M m g0 b ≤ paperOperationCap d M g0 := by
  obtain ⟨hlo, hband, hhi⟩ := paperBand_bounds d m hd b
  obtain ⟨hg, _, hgg0⟩ := paperBandG_bounds M g0 hM hg0 hsmall b
  have hs := paperBandLogStep_pos g0 hg0 hg01
  have hs' : paperBandLogStep g0 ≤ paperBandLogStep (paperBandG M g0 b) := by
    unfold paperBandLogStep
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (one_div_pos.mpr hg0) (one_div_le_one_div_of_le hg hgg0)) (by norm_num)
  have hwidth : paperBandHi d m b - paperBandLo d m b ≤ 2 * paperScheduleX d M := by
    have hl : 0 ≤ paperBandLo d m b :=
      (div_nonneg (paperScheduleX_pos d m hd).le (by positivity)).trans hlo
    have hx := paperScheduleX_mono d hd hm
    linarith
  have hr := (div_le_div_of_nonneg_left (sub_nonneg.mpr hband) hs hs').trans
    (div_le_div_of_nonneg_right hwidth hs.le)
  exact Nat.add_le_add_right (Nat.floor_mono hr) 1

theorem paperScheduleX_succ (d m : ℕ) :
    paperScheduleX d (m + 1) = paperScheduleBase d * paperScheduleX d m := by
  unfold paperScheduleX
  rw [pow_succ]
  ring

theorem paperScheduleX_ge_count (d M : ℕ) (hd : 1 ≤ d) :
    (M + 1 : ℝ) ≤ paperScheduleX d M := by
  have hb : 2 ≤ paperScheduleBase d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold paperScheduleBase
    linarith
  induction M with
  | zero => norm_num [paperScheduleX]
  | succ M ih =>
    rw [paperScheduleX_succ]
    push_cast
    have hx := (paperScheduleX_pos d M hd).le
    nlinarith

theorem paperOperationCap_real_bound (d M : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) :
    (paperOperationCap d M g0 : ℝ) ≤
      2 * paperScheduleX d M / paperBandLogStep g0 + 1 := by
  unfold paperOperationCap
  push_cast
  have hx := paperScheduleX_pos d M hd
  have hs := paperBandLogStep_pos g0 hg0 hg01
  have hf := Nat.floor_le
    (show 0 ≤ 2 * paperScheduleX d M / paperBandLogStep g0 by positivity)
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperBandLo
#print axioms BinaryFormMoat.GeometryIntegration.paperBandHi
#print axioms BinaryFormMoat.GeometryIntegration.paperBandG
#print axioms BinaryFormMoat.GeometryIntegration.paperBandOperationCount
#print axioms BinaryFormMoat.GeometryIntegration.paperOperationCap
#print axioms BinaryFormMoat.GeometryIntegration.paperBand_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandG_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandOperationCount_le_cap
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_ge_count
#print axioms BinaryFormMoat.GeometryIntegration.paperOperationCap_real_bound
