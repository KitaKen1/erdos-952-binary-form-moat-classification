import Integrations.PaperCoverageParameters435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- The manuscript's actual integer continuation quota, including its ceiling. -/
def paperCoverageTrials (d : ℕ) (T : ℝ) (i : ℕ) : ℕ :=
  Nat.ceil (T ^ ((6 / 5 : ℝ) * paperCheckpointBeta d i))

theorem paperCoverageTrials_bounds (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    T ^ ((6 / 5 : ℝ) * paperCheckpointBeta d i) ≤ (paperCoverageTrials d T i : ℝ) ∧
      (paperCoverageTrials d T i : ℝ) ≤ 2 * T ^ ((6 / 5 : ℝ) * paperCheckpointBeta d i) := by
  have hp : 1 ≤ T ^ ((6 / 5 : ℝ) * paperCheckpointBeta d i) :=
    Real.one_le_rpow hT (by positivity [paperCheckpointBeta_pos d i hd])
  refine ⟨Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ T ^ ((6 / 5 : ℝ) * paperCheckpointBeta d i))
  change (Nat.ceil _ : ℝ) ≤ _
  linarith

theorem paperCoverageTrials_pos (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    0 < paperCoverageTrials d T i := by
  have h := (paperCoverageTrials_bounds d hd T hT i).1
  have hp := Real.rpow_pos_of_pos (by linarith : 0 < T) ((6 / 5 : ℝ) * paperCheckpointBeta d i)
  exact_mod_cast (show (0 : ℝ) < paperCoverageTrials d T i by linarith)

/-- A dyadic prime pays at least half the extra fifth of beta in the trial
count. This supplies the scale in the empirical Bernoulli tail. -/
theorem paperCoverageTrials_residue_floor (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : 1 ≤ T)
    (i : ℕ) (p : ℝ) (hp : 0 < p) (hhi : p ≤ 2 * T) :
    Real.exp (paperCheckpointBeta d i * Real.log T / 5) / 2 ≤
      (paperCoverageTrials d T i : ℝ) * p ^ (-paperCheckpointBeta d i) := by
  let β := paperCheckpointBeta d i
  have hβ : 0 < β := paperCheckpointBeta_pos d i hd
  have hβ1 : β ≤ 1 := by
    have h := paperCheckpointBeta_antitone d hd (Nat.zero_le i)
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hz : paperCheckpointBeta d 0 ≤ 1 := by
      norm_num only [paperCheckpointBeta, pow_zero]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact h.trans hz
  have ht : 0 < T := by linarith
  have hc := (paperCoverageTrials_bounds d hd T hT i).1
  have hr : (2 : ℝ) ^ (-β) ≥ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hz : (2 : ℝ) ^ β ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by norm_num) _) hz
  have hpow : (2 * T) ^ (-β) ≤ p ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hp hhi (by linarith)
  have he : T ^ ((6 / 5 : ℝ) * β) * (2 * T) ^ (-β) =
      Real.exp (β * Real.log T / 5) * (2 : ℝ) ^ (-β) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le, Real.rpow_def_of_pos ht,
      Real.rpow_def_of_pos ht]
    rw [show Real.exp (Real.log T * ((6 / 5 : ℝ) * β)) *
      ((2 : ℝ) ^ (-β) * Real.exp (Real.log T * -β)) =
      (Real.exp (Real.log T * ((6 / 5 : ℝ) * β)) * Real.exp (Real.log T * -β)) *
      (2 : ℝ) ^ (-β) by ring, ← Real.exp_add]
    congr 2
    ring
  have h := mul_le_mul hc hpow (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * T) _)
    (Nat.cast_nonneg _)
  rw [he] at h
  exact (show Real.exp (β * Real.log T / 5) / 2 ≤
    Real.exp (β * Real.log T / 5) * (2 : ℝ) ^ (-β) by nlinarith [Real.exp_pos (β * Real.log T / 5)]).trans h

/-- The next native alphabet costs T^r_(i+1), while the recorded entropy
mass costs T^r_i. The exact radius gap leaves four fifths of beta. -/
theorem paperCoverageTrials_next_alphabet_ratio (d : ℕ) (hd : 1 ≤ d) (M : ℕ)
    (T : ℝ) (hT : 1 ≤ T) (i : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (paperCoverageTrials d T i : ℝ) * (C * paperCheckpointTarget d T (i + 1)) /
      (Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2) ≤
        4 * C * Real.exp (-(4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6) := by
  have ht : 0 < T := by linarith
  have hc := (paperCoverageTrials_bounds d hd T hT i).2
  have hprod := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ C * paperCheckpointTarget d T (i + 1) by positivity [paperCheckpointTarget_pos d T (i + 1)])
  have h := div_le_div_of_nonneg_right hprod
    (show 0 ≤ Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 by positivity)
  apply h.trans_eq
  rw [paperCheckpointTarget, Real.rpow_def_of_pos ht]
  calc
    _ = 4 * C * (Real.exp (Real.log T * ((6 / 5 : ℝ) * paperCheckpointBeta d i)) *
        Real.exp (paperCheckpointRadius d (i + 1) * Real.log T) /
        Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_sub, paperCheckpointRadius_succ d i hd]
      congr 2
      ring

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTrials
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTrials_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTrials_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTrials_residue_floor
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageTrials_next_alphabet_ratio
