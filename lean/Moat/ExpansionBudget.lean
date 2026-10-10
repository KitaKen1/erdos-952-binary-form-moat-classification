import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace BinaryFormMoat

/-- The size cap needed for geometric expansion is equivalent to an additive
logarithmic budget. This directly accepts the existing exp(-a*k) line tail. -/
theorem expansion_budget_of_log (g a : ℝ) (hg : 0 < g) (n t r k : ℕ)
    (hbudget : (r : ℝ) * Real.log g + ((n : ℝ) - 2 * t + 1) * Real.log 2 ≤ a * k) :
    g ^ r * (Real.exp (-a * k) * 2 ^ n) ≤ (2 : ℝ) ^ (2 * t) / 2 := by
  have hleft : g ^ r * (Real.exp (-a * k) * 2 ^ n) =
      Real.exp ((r : ℝ) * Real.log g + (-a * k) + (n : ℝ) * Real.log 2) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have hright : (2 : ℝ) ^ (2 * t) / 2 =
      Real.exp (((2 * t : ℕ) : ℝ) * Real.log 2 - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith only [hbudget]

end BinaryFormMoat
