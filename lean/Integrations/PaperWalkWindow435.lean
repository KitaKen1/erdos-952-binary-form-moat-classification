import Integrations.ConstructedSubsetBudget435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- The manuscript's actual transition window, including its floor. -/
def paperWalkWindow (U g : ℝ) : ℕ := ⌊Real.exp (g * U)⌋₊

theorem paperWalkWindow_pos (U g : ℝ) (h : 0 ≤ g * U) :
    0 < paperWalkWindow U g := by
  apply Nat.floor_pos.mpr
  simpa using Real.exp_le_exp.mpr h

theorem paperWalkWindow_log_bounds (U g : ℝ) (h : 0 ≤ g * U) :
    g * U ≤ Real.log (paperWalkWindow U g + 1 : ℕ) ∧
      Real.log (paperWalkWindow U g + 1 : ℕ) ≤ g * U + Real.log 2 := by
  have he : 1 ≤ Real.exp (g * U) := by simpa using Real.exp_le_exp.mpr h
  have hf := Nat.floor_le (Real.exp_pos (g * U)).le
  have hc := Nat.lt_floor_add_one (Real.exp (g * U))
  have hlo := Real.log_le_log (Real.exp_pos (g * U)) hc.le
  have hhi : ((paperWalkWindow U g + 1 : ℕ) : ℝ) ≤ 2 * Real.exp (g * U) := by
    dsimp [paperWalkWindow]
    push_cast
    linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (paperWalkWindow U g + 1 : ℕ)) hhi
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hl
  exact ⟨by simpa [paperWalkWindow, Real.log_exp, Nat.cast_add, Nat.cast_one] using hlo,
    by linarith⟩

/-- Fixed logarithmic area overhead for all bounded-step walks. -/
def paperWalkAreaConstant (D : ℕ) : ℝ :=
  Real.log (2 * (D + 1) ^ 2 : ℕ) + 2 * Real.log 2

theorem paperWalkAreaConstant_nonneg (D : ℕ) : 0 ≤ paperWalkAreaConstant D := by
  have hp : 1 ≤ 2 * (D + 1) ^ 2 := by
    have h : 0 < 2 * (D + 1) ^ 2 := by positivity
    omega
  exact add_nonneg (Real.log_nonneg (by exact_mod_cast hp))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))

/-- The integral area envelope has the same gU to 2gU scale as the manuscript,
uniformly in the walk and its starting point. Self-avoidance is not needed here. -/
theorem paperWalkWindow_area_log_bounds (z : ℕ → Point) (D : ℕ) (U g : ℝ)
    (h : 0 ≤ g * U)
    (hstep : ∀ t < paperWalkWindow U g,
      |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D) :
    g * U ≤ walkSeparationAreaLog z (paperWalkWindow U g) ∧
      walkSeparationAreaLog z (paperWalkWindow U g) ≤ 2 * g * U + paperWalkAreaConstant D := by
  let N := paperWalkWindow U g
  have hb := paperWalkWindow_log_bounds U g h
  have ha := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))
    (show ((N + 1 : ℕ) : ℝ) ≤ (prefixArea z N : ℝ) by exact_mod_cast (le_max_left _ _))
  have hu := prefixArea_upper z D N hstep
  have hl := Real.log_le_log
    (show (0 : ℝ) < (prefixArea z N : ℝ) by exact_mod_cast prefixArea_pos z N)
    (show (prefixArea z N : ℝ) ≤ (2 * (D + 1) ^ 2 * (N + 1) ^ 2 : ℕ) by exact_mod_cast hu)
  have he : Real.log (2 * (D + 1) ^ 2 * (N + 1) ^ 2 : ℕ) =
      Real.log (2 * (D + 1) ^ 2 : ℕ) + 2 * Real.log (N + 1 : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), Nat.cast_pow, Real.log_pow]
    norm_num
  rw [he] at hl
  change g * U ≤ Real.log (prefixArea z N : ℝ) ∧
    Real.log (prefixArea z N : ℝ) ≤ 2 * g * U + paperWalkAreaConstant D
  exact ⟨hb.1.trans ha, by unfold paperWalkAreaConstant; linarith [hb.2]⟩

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperWalkWindow
#print axioms BinaryFormMoat.GeometryIntegration.paperWalkWindow_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperWalkWindow_log_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperWalkAreaConstant
#print axioms BinaryFormMoat.GeometryIntegration.paperWalkAreaConstant_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.paperWalkWindow_area_log_bounds
