import Moat.Arithmetic
import Mathlib.Basic.Real.Basic

namespace BinaryFormMoat

/-- Counting replaces probability theory for the local root-selection estimate:
a nonzero direction is annihilated by at most one slope in any finite root set. -/
theorem slope_hit_count_le_one {K : Type*} [Field K] [DecidableEq K]
    (S : Finset K) (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    (S.filter (fun ρ => a = ρ * b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro ρ hρ σ hσ
  exact slope_unique a b ρ σ hab (Finset.mem_filter.mp hρ).2 (Finset.mem_filter.mp hσ).2

/-- The uniform finite average of the hit indicator is at most 1/d for d slopes. -/
theorem uniform_slope_hit_bound {K : Type*} [Field K] [DecidableEq K]
    (S : Finset K) (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    ((S.filter (fun ρ => a = ρ * b)).card : ℝ) / S.card ≤ 1 / (S.card : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast slope_hit_count_le_one S a b hab

/-- Weighting the uniform hit rate by the number of roots costs at most one.
This is the local d versus 1/d cancellation, proved by finite counting. -/
theorem weighted_uniform_slope_hit_bound {K : Type*} [Field K] [DecidableEq K]
    (S : Finset K) (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    (S.card : ℝ) * (((S.filter (fun ρ => a = ρ * b)).card : ℝ) / S.card) ≤ 1 := by
  by_cases hS : S.card = 0
  · simp [hS]
  · have hS' : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS
    rw [mul_div_cancel₀ _ hS']
    exact_mod_cast slope_hit_count_le_one S a b hab

end BinaryFormMoat
