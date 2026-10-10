import Integrations.PaperCheckpointHighEntropy435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

def paperCoverageDelta (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i / 64
def paperCoverageTau (i : ℕ) : ℝ := 3 / 8 - (1 / 2 : ℝ) ^ i / 8
def paperCoverageEta : ℕ → ℝ
  | 0 => 1 / 100
  | i + 1 => paperCoverageEta i * paperCoverageDelta i / 100

theorem paperCoverageDelta_pos (i : ℕ) : 0 < paperCoverageDelta i := by
  unfold paperCoverageDelta
  positivity

theorem paperCoverageDelta_le (i : ℕ) : paperCoverageDelta i ≤ 1 / 64 := by
  have h : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold paperCoverageDelta
  linarith

theorem paperCoverageDelta_succ (i : ℕ) : paperCoverageDelta (i + 1) = paperCoverageDelta i / 2 := by
  simp only [paperCoverageDelta, pow_succ]
  ring

theorem paperCoverageTau_zero : paperCoverageTau 0 = 1 / 4 := by norm_num [paperCoverageTau]

theorem paperCoverageTau_bounds (i : ℕ) : 1 / 4 ≤ paperCoverageTau i ∧ paperCoverageTau i < 3 / 8 := by
  have hl : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ i := pow_pos (by norm_num) _
  unfold paperCoverageTau
  constructor <;> linarith

theorem paperCoverageTau_succ (i : ℕ) :
    paperCoverageTau (i + 1) = paperCoverageTau i + 4 * paperCoverageDelta i := by
  simp only [paperCoverageTau, paperCoverageDelta, pow_succ]
  ring

theorem paperCoverageEta_zero : paperCoverageEta 0 = 1 / 100 := rfl
theorem paperCoverageEta_succ (i : ℕ) :
    paperCoverageEta (i + 1) = paperCoverageEta i * paperCoverageDelta i / 100 := rfl

theorem paperCoverageEta_pos (i : ℕ) : 0 < paperCoverageEta i := by
  induction i with
  | zero => norm_num [paperCoverageEta]
  | succ i ih => rw [paperCoverageEta_succ]; exact div_pos (mul_pos ih (paperCoverageDelta_pos i)) (by norm_num)

/-- Coarse logarithmic constants are obtained by comparison with powers of
2, rather than numerical approximation or new asymptotic machinery. -/
theorem paperCoverageStep_exp_lower (i : ℕ) :
    Real.exp (-((i : ℝ) + 13)) ≤ paperCoverageDelta i / 100 := by
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have h6400 : Real.log (6400 : ℝ) ≤ 13 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 6400)
      (by norm_num : (6400 : ℝ) ≤ 2 ^ 13)
    rw [Real.log_pow] at h
    norm_num at h
    nlinarith
  have he : Real.exp (-Real.log 2 * i - Real.log 6400) = paperCoverageDelta i / 100 := by
    rw [show -Real.log 2 * i - Real.log 6400 = (i : ℝ) * (-Real.log 2) + (-Real.log 6400) by ring,
      Real.exp_add, Real.exp_nat_mul]
    norm_num [Real.exp_neg, Real.exp_log, paperCoverageDelta]
    ring
  apply (Real.exp_le_exp.mpr ?_).trans_eq he
  nlinarith [mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg i)]

/-- An explicit O(i^2) lower bound for the paper's exceptional-coordinate
quota. It will be uniform over every stopping index J<=100*d*M. -/
theorem paperCoverageEta_exp_lower (i : ℕ) :
    Real.exp (-10 * ((i : ℝ) + 1) ^ 2) ≤ paperCoverageEta i := by
  induction i with
  | zero =>
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    have h100 : Real.log (100 : ℝ) ≤ 7 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
        (by norm_num : (100 : ℝ) ≤ 2 ^ 7)
      rw [Real.log_pow] at h
      norm_num at h
      nlinarith
    have h := Real.exp_le_exp.mpr (show (-10 : ℝ) ≤ -Real.log 100 by linarith)
    norm_num [Real.exp_neg, Real.exp_log, paperCoverageEta] at h ⊢
    exact h
  | succ i ih =>
    have hs := paperCoverageStep_exp_lower i
    have hp := mul_le_mul ih hs (Real.exp_pos _).le (paperCoverageEta_pos i).le
    rw [← Real.exp_add] at hp
    have hnum : -10 * (((i + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
        -10 * ((i : ℝ) + 1) ^ 2 + (-((i : ℝ) + 13)) := by
      push_cast
      nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    exact (Real.exp_le_exp.mpr hnum).trans (by simpa only [paperCoverageEta_succ, mul_div_assoc] using hp)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageDelta
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTau
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageEta
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageDelta_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageDelta_le
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageDelta_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTau_zero
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTau_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTau_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageEta_zero
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageEta_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageEta_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageStep_exp_lower
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageEta_exp_lower
