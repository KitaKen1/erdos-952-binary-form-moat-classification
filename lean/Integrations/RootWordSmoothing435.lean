import Integrations.DyadicRootWords435
import Integrations.TerminalSchedule435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- The common terminal smoothing supplies the candidate-hit quota for every
short word and every dyadic prime below the SAME global scale. -/
theorem shortWord_terminal_smoothing_quota (X : ℝ) (hX : 2 ≤ X)
    (T p L : ℕ) (hp : 1 ≤ p) (hT : (T : ℝ) ≤ X) (hL : L ≤ T)
    (hhi : p ≤ 2 * T) (τ : ℝ) (hτ : (1 : ℝ) / 4 ≤ τ) :
    (L : ℝ) / terminalSmoothingLength X ≤ (τ / p) / 2 := by
  have hx : 0 < X := by linarith
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlT : (L : ℝ) ≤ T := by exact_mod_cast hL
  have hl : (L : ℝ) ≤ X := hlT.trans hT
  have hi : (p : ℝ) ≤ 2 * X := by
    have h : (p : ℝ) ≤ 2 * T := by exact_mod_cast hhi
    linarith
  have hb := terminal_shift_ratio_source_bound L (terminalSmoothingLength X) X hx hl
    (terminalSmoothingLength_ge X)
  have h8 : (16 : ℝ) ≤ X ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX 8
    norm_num at h
    linarith
  have h9 : 16 * X ≤ X ^ 9 := by rw [pow_succ]; nlinarith
  have hh : 1 / X ^ 9 ≤ 1 / (16 * X) :=
    one_div_le_one_div_of_le (by positivity) h9
  have hq : 1 / (16 * X) ≤ (τ / p) / 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity : 0 < 16 * X) (by positivity : 0 < (p : ℝ) * 2)]
    nlinarith
  exact hb.trans (hh.trans hq)

/-- Choosing the actual dyadic root word removes the supplied smoothing
hypothesis from every fixed-coordinate passing-list theorem. -/
theorem rootWord_terminal_smoothing_quota (d T p : ℕ) (hd : 1 ≤ d) (hT₀ : 1 ≤ T)
    (X : ℝ) (hX : 2 ≤ X) (hT : (T : ℝ) ≤ X) (hp : 1 ≤ p) (hhi : p ≤ 2 * T)
    (τ : ℝ) (hτ : (1 : ℝ) / 4 ≤ τ) :
    (rootWordLength d T : ℝ) / terminalSmoothingLength X ≤ (τ / p) / 2 :=
  shortWord_terminal_smoothing_quota X hX T p (rootWordLength d T) hp hT
    (rootWordLength_le d T hd hT₀) hhi τ hτ

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.shortWord_terminal_smoothing_quota
#print axioms BinaryFormMoat.EntropyIntegration.rootWord_terminal_smoothing_quota
