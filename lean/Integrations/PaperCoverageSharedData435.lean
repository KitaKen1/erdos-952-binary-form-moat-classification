import Integrations.PaperCoverageTrials435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- The four-fifths radius gap absorbs both integer rounding and the entire
native alphabet constant at ONE threshold, uniformly for all i<J. -/
theorem paperCoverageSharedData_eventually (C : ℝ) (hC : 0 < C) :
    ∃ M0 : ℕ, 2 ≤ M0 ∧ ∀ M ≥ M0, ∀ (hM : 1 ≤ M), ∀ d : ℕ, ∀ T : ℝ, ∀ i : ℕ,
      i < paperCheckpointStop d M T hM →
        4 * C * Real.exp (-(4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6) ≤
          Real.exp (-(M : ℝ) ^ 3) := by
  let M0 := Nat.ceil (Real.log (4 * C)) + 10
  refine ⟨M0, by omega, ?_⟩
  intro M hM hM1 d T i hi
  have hMR : (10 : ℝ) ≤ M := by exact_mod_cast (show 10 ≤ M by omega)
  have hMP : (0 : ℝ) < M := by linarith
  have hc : Real.log (4 * C) ≤ M := by
    have hceil := Nat.le_ceil (Real.log (4 * C))
    have hn : (Nat.ceil (Real.log (4 * C)) : ℝ) ≤ M := by exact_mod_cast (show Nat.ceil (Real.log (4 * C)) ≤ M by omega)
    exact hceil.trans hn
  have h36 : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h16 : (M : ℝ) ≤ (M : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ M) (by norm_num : 1 ≤ 6)
  have h720 : (M : ℝ) ^ 7 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have he7 : (M : ℝ) ^ 7 = (M : ℝ) ^ 6 * M := by ring
  have hb := paperCheckpointStop_before d M T hM1 i hi
  have hnum : Real.log (4 * C) - (4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6 ≤
      -(M : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hMR (pow_nonneg hMP.le 6)]
  calc
    _ = Real.exp (Real.log (4 * C) - (4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6) := by
      rw [show Real.log (4 * C) - (4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6 =
        Real.log (4 * C) + (-(4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6) by ring,
        Real.exp_add (Real.log (4 * C)), Real.exp_log (by positivity : 0 < 4 * C)]
    _ ≤ _ := Real.exp_le_exp.mpr hnum

def paperCoverageSharedDataThreshold (C : ℝ) (hC : 0 < C) : ℕ :=
  Classical.choose (paperCoverageSharedData_eventually C hC)

theorem paperCoverageSharedDataThreshold_spec (C : ℝ) (hC : 0 < C) :
    2 ≤ paperCoverageSharedDataThreshold C hC ∧
      ∀ M ≥ paperCoverageSharedDataThreshold C hC, ∀ (hM : 1 ≤ M), ∀ d : ℕ, ∀ T : ℝ, ∀ i : ℕ,
        i < paperCheckpointStop d M T hM →
          4 * C * Real.exp (-(4 / 5 : ℝ) * paperCheckpointBeta d i * Real.log T + 4 * (M : ℝ) ^ 6) ≤
            Real.exp (-(M : ℝ) ^ 3) :=
  Classical.choose_spec (paperCoverageSharedData_eventually C hC)

/-- Scalar interface to the actual posterior shared-data entropy budget.
The record mass is already supplied by the constructed middle certificate. -/
theorem paperCoverageSharedData_budget (d : ℕ) (hd : 1 ≤ d) (M : ℕ) (hM : 1 ≤ M)
    (T : ℝ) (hT : 1 ≤ T) (i : ℕ) (hi : i < paperCheckpointStop d M T hM)
    (C : ℝ) (hC : 0 < C) (hlarge : paperCoverageSharedDataThreshold C hC ≤ M)
    (A mass : ℝ) (hA : A ≤ C * paperCheckpointTarget d T (i + 1))
    (hmass : Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤ mass) :
    (paperCoverageTrials d T i : ℝ) * A ≤ Real.exp (-(M : ℝ) ^ 3) * mass := by
  have hratio := (paperCoverageTrials_next_alphabet_ratio d hd M T hT i C hC.le).trans
    ((paperCoverageSharedDataThreshold_spec C hC).2 M hlarge hM d T i hi)
  have hm := (div_le_iff₀ (show 0 < Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 by positivity)).mp hratio
  exact (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)).trans
    (hm.trans (mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le))

/-- The ACTUAL future displacement alphabet at checkpoint i+1, rather than
an alphabet conditioned on a particular future start, fits the data budget. -/
theorem paperMiddleCheckpoint_shared_data_budget {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    (g0 : ℝ) (m : Fin (M + 1)) (T : ℝ) (hT : 1 ≤ T) (i R : ℕ)
    (hi : i < paperCheckpointStop d M T hM) (hfit)
    (hg1 : paperScheduleMiddleG M < 1)
    (hhi : Real.log (paperCheckpointTarget d T (i + 1)) ≤ paperBandHi d m.val 1)
    (hV : 1 ≤ paperCheckpointTarget d T (i + 1))
    (hfuture : Real.log (paperFutureShift (paperMiddleCheckpointOp (d := d) g0 m T (i + 1) hfit) + 1 : ℕ) ≤
      2 * (paperOpG (paperMiddleCheckpointOp g0 m T (i + 1) hfit) *
        paperOpU (paperMiddleCheckpointOp g0 m T (i + 1) hfit)))
    (hlarge : paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
      (by have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega)); linarith) ≤ M)
    (mass : ℝ) (hmass : Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤ mass) :
    (paperCoverageTrials d T i : ℝ) *
      (2 * Real.log (2 * ((R + 1) * paperFutureShift (paperMiddleCheckpointOp (d := d) g0 m T (i + 1) hfit)) + 1 : ℕ)) ≤
        Real.exp (-(M : ℝ) ^ 3) * mass := by
  have hC : 0 < 4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega))
    linarith
  exact paperCoverageSharedData_budget d hd M hM T hT i hi _ hC hlarge _ mass
    (paperMiddleCheckpoint_native_alphabet g0 m T (i + 1) R hfit hg1 hhi hV hfuture) hmass

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageSharedData_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageSharedDataThreshold
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageSharedDataThreshold_spec
#print axioms BinaryFormMoat.GeometryIntegration.paperCoverageSharedData_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpoint_shared_data_budget
