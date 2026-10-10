import Integrations.PaperCoverageApplication435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- Walk-independent scalar inputs for the already proved actual backward
coverage theorem. They do not choose a second prime batch. -/
structure PaperInformationThresholds (d R M : ℕ) (hd : 1 ≤ d) (g0 : ℝ) : Prop where
  two : 2 ≤ M
  accuracy : paperMiddleAccuracyThreshold ≤ M
  base : paperTerminalCoverageThreshold d hd ≤ M
  margins : paperCoverageMarginsThreshold d hd ≤ M
  tail : paperCoverageTailThreshold d hd ≤ M
  shared : paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
    (by
      have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega))
      linarith) ≤ M
  future : ∀ o ∈ paperScheduledOps d M g0,
    Real.log (paperFutureShift o + 1 : ℕ) ≤ 2 * (paperOpG o * paperOpU o)

/-- ONE threshold handles all coverage scalar inputs and actual future
bounds, before prime selection, growing indices, source laws and walks. -/
theorem paperInformationThresholds_eventually (d R : ℕ) (hd : 1 ≤ d)
    (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ M0 : ℕ, ∀ M ≥ M0, PaperInformationThresholds d R M hd g0 := by
  obtain ⟨Mf, hf⟩ := paperSchedule_uniform_future_shift d hd g0 hg0 (by linarith)
  let Ma := paperMiddleAccuracyThreshold
  let Mb := paperTerminalCoverageThreshold d hd
  let Mm := paperCoverageMarginsThreshold d hd
  let Mt := paperCoverageTailThreshold d hd
  have hC : 0 < 4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    have h := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega) : (1 : ℝ) ≤ (2 * (R + 1) + 1 : ℕ))
    linarith
  let Ms := paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) hC
  refine ⟨2 + Ma + Mb + Mm + Mt + Ms + Mf, ?_⟩
  intro M hM
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hf M (by omega)⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperInformationThresholds
#print axioms BinaryFormMoat.GeometryIntegration.paperInformationThresholds_eventually
