import Integrations.PaperCoverageMargins435
import Integrations.PaperCoverageSharedData435
import Integrations.PaperTerminalCoverage435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- The actual integer trial quota gives the empirical union-tail input at
ONE threshold for every window, every stopping index and every dyadic prime. -/
theorem paperCoverageTail_eventually (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, 2 ≤ M0 ∧ ∀ M ≥ M0, ∀ (hM : 1 ≤ M), ∀ T : ℝ, 2 ≤ T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M → ∀ i : ℕ,
        i < paperCheckpointStop d M T hM → ∀ p : ℝ, T ≤ p → p ≤ 2 * T →
          p * Real.exp (-(paperCoverageDelta i) ^ 2 * (paperCoverageTrials d T i : ℝ) *
            p ^ (-paperCheckpointBeta d i) / 2) ≤ paperCoverageDelta i / 100 := by
  let K : ℝ := 100 * d
  let b := Real.log (paperScheduleBase d)
  let M0 := Nat.ceil (5 * (2 * K + b + 31)) + 20
  refine ⟨M0, by omega, ?_⟩
  intro M hlarge hM T hT hlog i hi p hlo hhi
  have hMR : (20 : ℝ) ≤ M := by exact_mod_cast (show 20 ≤ M by omega)
  have hM1R : (1 : ℝ) ≤ M := by linarith
  have hMP : (0 : ℝ) < M := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (100 : ℝ) ≤ K := by dsimp [K]; nlinarith
  have hb : 0 < b := Real.log_pos (paperScheduleBase_gt_one d hd)
  have hCM : 5 * (2 * K + b + 31) < (M : ℝ) := by
    have hc := Nat.le_ceil (5 * (2 * K + b + 31))
    have hn : (Nat.ceil (5 * (2 * K + b + 31)) : ℝ) + 20 ≤ M := by exact_mod_cast hlarge
    linarith
  have hiR : (i : ℝ) ≤ K * M := by
    have h := (Nat.le_of_lt hi).trans (paperCheckpointStop_linear_bound d M hd T hM hlog)
    dsimp only [K]
    exact_mod_cast h
  have h220 : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hM1R (by norm_num)
  have hroom : (b + 1) * M ≤ (M : ℝ) ^ 20 / 5 - 2 * (K * M + 13) - 4 := by
    nlinarith [mul_lt_mul_of_pos_right hCM hMP]
  have hbStop := paperCheckpointStop_before d M T hM i hi
  have hδ := paperCoverageStep_exp_lower i
  have hweak : Real.exp (-((i : ℝ) + 13)) ≤ paperCoverageDelta i := by linarith [paperCoverageDelta_pos i]
  have hδ2 : Real.exp (-2 * ((i : ℝ) + 13)) ≤ (paperCoverageDelta i) ^ 2 := by
    have h := mul_self_le_mul_self (Real.exp_pos _).le hweak
    rw [← Real.exp_add] at h
    convert h using 1 <;> ring
  have hpP : 0 < p := by linarith
  have hn := paperCoverageTrials_residue_floor d hd T (by linarith) i p hpP hhi
  let E := (paperCoverageDelta i) ^ 2 * (paperCoverageTrials d T i : ℝ) * p ^ (-paperCheckpointBeta d i) / 2
  have hprod := div_le_div_of_nonneg_right
    (mul_le_mul hδ2 hn (by positivity : 0 ≤ Real.exp (paperCheckpointBeta d i * Real.log T / 5) / 2)
      (sq_nonneg (paperCoverageDelta i))) (by norm_num : (0 : ℝ) ≤ 2)
  have he : Real.exp (paperCheckpointBeta d i * Real.log T / 5 - 2 * ((i : ℝ) + 13)) / 4 ≤ E := by
    convert hprod using 1
    · rw [show paperCheckpointBeta d i * Real.log T / 5 - 2 * ((i : ℝ) + 13) =
        -2 * ((i : ℝ) + 13) + paperCheckpointBeta d i * Real.log T / 5 by ring, Real.exp_add]
      ring
    · dsimp [E]; ring
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbase : Real.exp ((b + 1) * M) ≤ E := by
    calc
      _ ≤ Real.exp (paperCheckpointBeta d i * Real.log T / 5 - 2 * ((i : ℝ) + 13) - 4) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (paperCheckpointBeta d i * Real.log T / 5 - 2 * ((i : ℝ) + 13)) / Real.exp 4 := Real.exp_sub _ _
      _ ≤ Real.exp (paperCheckpointBeta d i * Real.log T / 5 - 2 * ((i : ℝ) + 13)) / 4 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h4
      _ ≤ _ := he
  have hX : 2 * K + 30 ≤ paperScheduleX d M := by
    have hx := paperScheduleX_mono d hd (show 2 ≤ M by omega)
    have hbase : paperScheduleX d 2 = K ^ 2 := by rfl
    rw [hbase] at hx
    nlinarith
  have hlogp : Real.log p ≤ 1 + (21 / 20 : ℝ) * paperScheduleX d M := by
    have h := Real.log_le_log hpP hhi
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)] at h
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    linarith
  have hexp : paperScheduleX d M * ((M : ℝ) + 1) ≤ Real.exp ((b + 1) * M) := by
    rw [paperScheduleX_exp d M hd, show (b + 1) * (M : ℝ) = b * M + M by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp (M : ℝ)) (Real.exp_pos _).le
  have hgap : Real.log p - E ≤ -((i : ℝ) + 13) := by
    nlinarith [mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ (M : ℝ) - 21 / 20 by linarith)]
  calc
    _ = Real.exp (Real.log p - E) := by
      have hE : -(paperCoverageDelta i) ^ 2 * (paperCoverageTrials d T i : ℝ) *
          p ^ (-paperCheckpointBeta d i) / 2 = -E := by dsimp [E]; ring
      rw [hE]
      rw [Real.exp_sub, Real.exp_log hpP, Real.exp_neg]
      ring
    _ ≤ Real.exp (-((i : ℝ) + 13)) := Real.exp_le_exp.mpr hgap
    _ ≤ _ := hδ

def paperCoverageTailThreshold (d : ℕ) (hd : 1 ≤ d) : ℕ :=
  Classical.choose (paperCoverageTail_eventually d hd)

theorem paperCoverageTailThreshold_spec (d : ℕ) (hd : 1 ≤ d) :
    2 ≤ paperCoverageTailThreshold d hd ∧ ∀ M ≥ paperCoverageTailThreshold d hd,
      ∀ (hM : 1 ≤ M), ∀ T : ℝ, 2 ≤ T → Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M →
      ∀ i : ℕ, i < paperCheckpointStop d M T hM → ∀ p : ℝ, T ≤ p → p ≤ 2 * T →
        p * Real.exp (-(paperCoverageDelta i) ^ 2 * (paperCoverageTrials d T i : ℝ) *
          p ^ (-paperCheckpointBeta d i) / 2) ≤ paperCoverageDelta i / 100 :=
  Classical.choose_spec (paperCoverageTail_eventually d hd)

/-- All scalar inputs to the existing one-step transfer, together with the
native alphabet cost, are supplied at ONE threshold before ALL growing
families. The conditional next-step coverage premise is deliberately absent. -/
theorem paperCoverage_uniform_numeric_budgets (d R : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, 2 ≤ M0 ∧ ∀ M ≥ M0, ∀ (hM : 1 ≤ M), ∀ m : ℕ, m ≤ M → ∀ T : ℝ, 2 ≤ T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m → ∀ i : ℕ,
        i < paperCheckpointStop d M T hM →
          0 < paperCoverageTrials d T i ∧
          Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) + Real.exp (-(M : ℝ) ^ 3) ≤
            paperCoverageEta i * paperCoverageDelta i * paperCheckpointBeta d (i + 1) / 16 ∧
          Real.log (Real.exp 1 / (paperCoverageDelta i / 2)) ≤
            paperCheckpointBeta d (i + 1) / 4 * Real.log T ∧
          (∀ p : ℝ, T ≤ p → p ≤ 2 * T →
            (paperCoverageDelta i)⁻¹ < p ^ (paperCheckpointBeta d (i + 1) / 2) ∧
            p * Real.exp (-(paperCoverageDelta i) ^ 2 * (paperCoverageTrials d T i : ℝ) *
              p ^ (-paperCheckpointBeta d i) / 2) ≤ paperCoverageDelta i / 100) ∧
          (∀ A mass : ℝ,
            A ≤ (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) * paperCheckpointTarget d T (i + 1) →
            Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤ mass →
              (paperCoverageTrials d T i : ℝ) * A ≤ Real.exp (-(M : ℝ) ^ 3) * mass) := by
  have hC : 0 < 4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega))
    linarith
  let a := paperCoverageMarginsThreshold d hd
  let b := paperCoverageTailThreshold d hd
  let c := paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) hC
  refine ⟨a + b + c + 2, by omega, ?_⟩
  intro M hlarge hM m hm T hT hlog i hi
  have ha : a ≤ M := by omega
  have hb : b ≤ M := by omega
  have hc : c ≤ M := by omega
  have hlogM : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M :=
    hlog.trans (mul_le_mul_of_nonneg_left (paperScheduleX_mono d hd hm) (by norm_num))
  have hmar := (paperCoverageMarginsThreshold_spec d hd).2 M ha hM T hT hlogM i hi
  refine ⟨paperCoverageTrials_pos d hd T (by linarith) i, hmar.1, hmar.2.2, ?_, ?_⟩
  · intro p hlo hhi
    exact ⟨hmar.2.1 p hlo, (paperCoverageTailThreshold_spec d hd).2 M hb hM T hT hlogM i hi p hlo hhi⟩
  · intro A mass hA hmass
    exact paperCoverageSharedData_budget d hd M hM T (by linarith) i hi _ hC hc A mass hA hmass

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTail_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTailThreshold
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTailThreshold_spec
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverage_uniform_numeric_budgets
