import Integrations.PaperCoverageTrials435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

theorem paperCoverageDelta_inverse_log_le (i : ℕ) :
    Real.log (paperCoverageDelta i)⁻¹ ≤ (i : ℝ) + 13 := by
  have hp := paperCoverageDelta_pos i
  have h := paperCoverageStep_exp_lower i
  have hweak : Real.exp (-((i : ℝ) + 13)) ≤ paperCoverageDelta i := by linarith
  have hl := Real.log_le_log (Real.exp_pos _) hweak
  rw [Real.log_exp] at hl
  rw [Real.log_inv]
  linarith

theorem paperCheckpointBeta_exp_lower (d i : ℕ) (hd : 1 ≤ d) :
    Real.exp (-((i : ℝ) + Real.log (200 * d))) ≤ paperCheckpointBeta d i := by
  have hdP : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have he : Real.exp (-(i : ℝ) * Real.log 2 - Real.log (200 * d)) = paperCheckpointBeta d i := by
    rw [show -(i : ℝ) * Real.log 2 - Real.log (200 * d) =
      (i : ℝ) * (-Real.log 2) + (-Real.log (200 * d)) by ring, Real.exp_add, Real.exp_nat_mul]
    have h200 : 0 < 200 * (d : ℝ) := by positivity
    norm_num [Real.exp_neg, Real.exp_log, h200, paperCheckpointBeta]
    ring
  apply (Real.exp_le_exp.mpr ?_).trans_eq he
  nlinarith [mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg i)]

/-- A deliberately coarse quadratic logarithmic cost for the exact paper
quota, avoiding asymptotics in the growing checkpoint index. -/
def paperCoverageLogCost (d i : ℕ) : ℝ :=
  10 * ((i : ℝ) + 1) ^ 2 + 2 * i + 18 + Real.log (200 * d)

theorem paperCoverageQuota_exp_lower (d i : ℕ) (hd : 1 ≤ d) :
    Real.exp (-paperCoverageLogCost d i) ≤
      paperCoverageEta i * paperCoverageDelta i * paperCheckpointBeta d (i + 1) / 16 := by
  have hδ : Real.exp (-((i : ℝ) + 13)) ≤ paperCoverageDelta i := by
    linarith [paperCoverageStep_exp_lower i, paperCoverageDelta_pos i]
  have hβ := paperCheckpointBeta_exp_lower d (i + 1) hd
  have hp := mul_le_mul (paperCoverageEta_exp_lower i) hδ (Real.exp_pos _).le (paperCoverageEta_pos i).le
  have hp' := mul_le_mul hp hβ (Real.exp_pos _).le
    (mul_pos (paperCoverageEta_pos i) (paperCoverageDelta_pos i)).le
  have hp'' := div_le_div_of_nonneg_right hp' (by norm_num : (0 : ℝ) ≤ 16)
  have hlog16 : Real.log (16 : ℝ) ≤ 4 := by
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  have he : Real.exp (-10 * ((i : ℝ) + 1) ^ 2) * Real.exp (-((i : ℝ) + 13)) *
      Real.exp (-(((i + 1 : ℕ) : ℝ) + Real.log (200 * d))) / 16 =
        Real.exp (-10 * ((i : ℝ) + 1) ^ 2 - ((i : ℝ) + 13) -
          (((i + 1 : ℕ) : ℝ) + Real.log (200 * d)) - Real.log 16) := by
    rw [← Real.exp_add, ← Real.exp_add]
    have h := Real.exp_sub (-10 * ((i : ℝ) + 1) ^ 2 + (-((i : ℝ) + 13)) +
      (-(((i + 1 : ℕ) : ℝ) + Real.log (200 * d)))) (Real.log 16)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 16)] at h
    exact h.symm.trans (by congr 1)
  rw [he] at hp''
  exact (Real.exp_le_exp.mpr (by unfold paperCoverageLogCost; push_cast; linarith)).trans hp''

/-- ONE threshold supplies all entropy-error, rounding-margin and log-gap
inputs to one-step coverage, for ALL i<J and ALL dyadic primes. -/
theorem paperCoverageMargins_eventually (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, 2 ≤ M0 ∧ ∀ M ≥ M0, ∀ (hM : 1 ≤ M), ∀ T : ℝ, 2 ≤ T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M → ∀ i : ℕ,
        i < paperCheckpointStop d M T hM →
          Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) + Real.exp (-(M : ℝ) ^ 3) ≤
            paperCoverageEta i * paperCoverageDelta i * paperCheckpointBeta d (i + 1) / 16 ∧
          (∀ p : ℝ, T ≤ p → (paperCoverageDelta i)⁻¹ < p ^ (paperCheckpointBeta d (i + 1) / 2)) ∧
          Real.log (Real.exp 1 / (paperCoverageDelta i / 2)) ≤
            paperCheckpointBeta d (i + 1) / 4 * Real.log T := by
  let K : ℝ := 100 * d
  let C := 10 * (K + 1) ^ 2 + 2 * K + 18 + Real.log (200 * d)
  let M0 := Nat.ceil (8 * C + 8 * K + 200) + 20
  refine ⟨M0, by omega, ?_⟩
  intro M hlarge hM T hT hlog i hi
  have hMR : (20 : ℝ) ≤ M := by exact_mod_cast (show 20 ≤ M by omega)
  have hM1R : (1 : ℝ) ≤ M := by linarith
  have hMP : (0 : ℝ) < M := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 < K := by dsimp [K]; positivity
  have hL0 : 0 ≤ Real.log (200 * (d : ℝ)) := Real.log_nonneg (by nlinarith)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCM : 8 * C + 8 * K + 200 < (M : ℝ) := by
    have hc := Nat.le_ceil (8 * C + 8 * K + 200)
    have hn : (Nat.ceil (8 * C + 8 * K + 200) : ℝ) + 20 ≤ M := by exact_mod_cast hlarge
    linarith
  have hiR : (i : ℝ) ≤ K * M := by
    have h := (Nat.le_of_lt hi).trans (paperCheckpointStop_linear_bound d M hd T hM hlog)
    dsimp only [K]
    exact_mod_cast h
  have hsq : ((i : ℝ) + 1) ^ 2 ≤ (K + 1) ^ 2 * (M : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
      (by nlinarith : (i : ℝ) + 1 ≤ (K + 1) * M)
    nlinarith
  have hM2 : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hcost : paperCoverageLogCost d i ≤ C * (M : ℝ) ^ 2 := by
    dsimp [paperCoverageLogCost, C]
    nlinarith [mul_le_mul_of_nonneg_left hM2 hK.le, one_le_pow₀ hM1R (n := 2),
      mul_le_mul_of_nonneg_left (one_le_pow₀ hM1R (n := 2)) hL0]
  have h2L : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one] at h
    linarith
  have hnum : paperCoverageLogCost d i + 1 ≤ (M : ℝ) ^ 3 / 4 := by
    have he : (M : ℝ) ^ 3 = M * (M : ℝ) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_right (show 4 * (C + 1) ≤ (M : ℝ) by linarith) (sq_nonneg (M : ℝ)),
      one_le_pow₀ hM1R (n := 2)]
  have heps : Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) ≤ Real.exp (-(M : ℝ) ^ 3 / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [pow_nonneg hMP.le 3])
  have hκ : Real.exp (-(M : ℝ) ^ 3) ≤ Real.exp (-(M : ℝ) ^ 3 / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [pow_nonneg hMP.le 3])
  have herror : Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) + Real.exp (-(M : ℝ) ^ 3) ≤
      Real.exp (-paperCoverageLogCost d i) := by
    calc
      _ ≤ 2 * Real.exp (-(M : ℝ) ^ 3 / 4) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-(M : ℝ) ^ 3 / 4) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (1 - (M : ℝ) ^ 3 / 4) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hb := paperCheckpointStop_before d M T hM i hi
  have hβnext : paperCheckpointBeta d (i + 1) * Real.log T > (M : ℝ) ^ 20 / 2 := by
    rw [paperCheckpointBeta_succ]
    nlinarith
  have h320 : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hM1R (by norm_num)
  have hKM : K * M + 15 < (M : ℝ) ^ 20 / 8 := by
    have hK1 : 8 * (K + 15) < (M : ℝ) := by linarith
    have hMM : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := pow_le_pow_right₀ hM1R (by norm_num)
    nlinarith [mul_lt_mul_of_pos_right hK1 hMP]
  refine ⟨herror.trans (paperCoverageQuota_exp_lower d i hd), ?_, ?_⟩
  · intro p hp
    have hpP : 0 < p := by linarith
    have hl := Real.log_le_log (by linarith : 0 < T) hp
    have hδ := paperCoverageDelta_inverse_log_le i
    have hnext := mul_le_mul_of_nonneg_left hl (paperCheckpointBeta_pos d (i + 1) hd).le
    apply (Real.log_lt_log_iff (inv_pos.mpr (paperCoverageDelta_pos i)) (Real.rpow_pos_of_pos hpP _)).mp
    rw [Real.log_rpow hpP]
    nlinarith
  · have h2 : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    have hδ := paperCoverageDelta_inverse_log_le i
    rw [Real.log_div (Real.exp_pos 1).ne' (by positivity [paperCoverageDelta_pos i] : paperCoverageDelta i / 2 ≠ 0),
      Real.log_exp, Real.log_div (paperCoverageDelta_pos i).ne' (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.log_inv] at hδ
    nlinarith

def paperCoverageMarginsThreshold (d : ℕ) (hd : 1 ≤ d) : ℕ :=
  Classical.choose (paperCoverageMargins_eventually d hd)

theorem paperCoverageMarginsThreshold_spec (d : ℕ) (hd : 1 ≤ d) :
    2 ≤ paperCoverageMarginsThreshold d hd ∧ ∀ M ≥ paperCoverageMarginsThreshold d hd,
      ∀ (hM : 1 ≤ M), ∀ T : ℝ, 2 ≤ T → Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M →
      ∀ i : ℕ, i < paperCheckpointStop d M T hM →
        Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) + Real.exp (-(M : ℝ) ^ 3) ≤
          paperCoverageEta i * paperCoverageDelta i * paperCheckpointBeta d (i + 1) / 16 ∧
        (∀ p : ℝ, T ≤ p → (paperCoverageDelta i)⁻¹ < p ^ (paperCheckpointBeta d (i + 1) / 2)) ∧
        Real.log (Real.exp 1 / (paperCoverageDelta i / 2)) ≤
          paperCheckpointBeta d (i + 1) / 4 * Real.log T :=
  Classical.choose_spec (paperCoverageMargins_eventually d hd)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageDelta_inverse_log_le
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointBeta_exp_lower
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageLogCost
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageQuota_exp_lower
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageMargins_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageMarginsThreshold
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageMarginsThreshold_spec
