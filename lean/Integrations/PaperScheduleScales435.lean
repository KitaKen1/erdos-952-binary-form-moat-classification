import Integrations.PaperEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

def paperScheduleBase (d : ℕ) : ℝ := 100 * d
def paperScheduleX (d m : ℕ) : ℝ := paperScheduleBase d ^ m
def paperScheduleMinU (d M : ℕ) : ℝ :=
  Real.exp (paperScheduleX d ((M + 1) / 2) / (20 * d))
def paperScheduleMinG (M : ℕ) : ℝ := Real.exp (-100 * (M : ℝ) ^ 20)
def paperScheduleMiddleG (M : ℕ) : ℝ := Real.exp (-(M : ℝ) ^ 3)
def paperScheduleMaxT (d M : ℕ) : ℝ := Real.exp ((21 / 20 : ℝ) * paperScheduleX d M)

theorem paperScheduleBase_gt_one (d : ℕ) (hd : 1 ≤ d) : 1 < paperScheduleBase d := by
  have h : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold paperScheduleBase
  linarith

theorem paperScheduleX_pos (d m : ℕ) (hd : 1 ≤ d) : 0 < paperScheduleX d m :=
  pow_pos ((by norm_num : (0 : ℝ) < 1).trans (paperScheduleBase_gt_one d hd)) _

theorem paperScheduleX_exp (d m : ℕ) (hd : 1 ≤ d) :
    paperScheduleX d m = Real.exp (Real.log (paperScheduleBase d) * m) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log
    ((by norm_num : (0 : ℝ) < 1).trans (paperScheduleBase_gt_one d hd))]
  rfl

theorem paperScheduleX_mono (d : ℕ) (hd : 1 ≤ d) : Monotone (paperScheduleX d) :=
  fun _ _ h => pow_le_pow_right₀ (paperScheduleBase_gt_one d hd).le h

theorem paperScheduleX_half_lower (d M : ℕ) (hd : 1 ≤ d) :
    Real.exp ((Real.log (paperScheduleBase d) / 2) * M) ≤
      paperScheduleX d ((M + 1) / 2) := by
  have hn : M ≤ 2 * ((M + 1) / 2) := by omega
  have hr : (M : ℝ) ≤ 2 * (((M + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (paperScheduleBase d) := Real.log_pos (paperScheduleBase_gt_one d hd)
  rw [paperScheduleX_exp d _ hd]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem paperScheduleMinU_le_stage (d M m : ℕ) (hd : 1 ≤ d)
    (hm : (M + 1) / 2 ≤ m) (U : ℝ) (hU : 0 < U)
    (hlog : paperScheduleX d m / (20 * d) ≤ Real.log U) :
    paperScheduleMinU d M ≤ U := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  apply (Real.exp_le_exp.mpr ((div_le_div_of_nonneg_right
    (paperScheduleX_mono d hd hm) (by positivity)).trans hlog)).trans_eq
  exact Real.exp_log hU

theorem paperScheduleMaxT_ge_stage (d M m : ℕ) (hd : 1 ≤ d) (hm : m ≤ M)
    (T : ℝ) (hT : 0 < T) (hlog : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m) :
    T ≤ paperScheduleMaxT d M := by
  rw [← Real.exp_log hT]
  apply Real.exp_le_exp.mpr
  exact hlog.trans (mul_le_mul_of_nonneg_left (paperScheduleX_mono d hd hm) (by norm_num))

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleBase
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMinU
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMinG
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMiddleG
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMaxT
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleBase_gt_one
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_exp
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_mono
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleX_half_lower
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMinU_le_stage
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleMaxT_ge_stage
