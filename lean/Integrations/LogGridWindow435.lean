import Integrations.PaperGeometricIndices435
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- The exact integer grid in one logarithmic window, with both endpoints
included. This is a symbolic finite set, not an enumerated large range. -/
def logGridWindow (X h : ℝ) : Finset ℕ :=
  Finset.Icc ⌈X / h⌉₊ ⌊((21 / 20 : ℝ) * X) / h⌋₊

theorem mem_logGridWindow (X h : ℝ) (hX : 0 ≤ X) (hh : 0 < h) (j : ℕ) :
    j ∈ logGridWindow X h ↔ X ≤ (j : ℝ) * h ∧
      (j : ℝ) * h ≤ (21 / 20 : ℝ) * X := by
  rw [logGridWindow, Finset.mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff (by positivity : 0 ≤ ((21 / 20 : ℝ) * X) / h)]
  exact and_congr (div_le_iff₀ hh) (le_div_iff₀ hh)

/-- Floor/ceiling lose at most one grid cell from the interval's length.
X>=40h leaves half the nominal width, with explicit constants. -/
theorem logGridWindow_card_lower (X h : ℝ) (hh : 0 < h) (hlarge : 40 * h ≤ X) :
    X / (40 * h) ≤ ((logGridWindow X h).card : ℝ) := by
  let L := X / h
  let U := ((21 / 20 : ℝ) * X) / h
  let l := ⌈L⌉₊
  let u := ⌊U⌋₊
  have hX : 0 < X := by linarith
  have hceil : (l : ℝ) < L + 1 := Nat.ceil_lt_add_one (by dsimp [L]; positivity)
  have hfloor : U < (u : ℝ) + 1 := Nat.lt_floor_add_one U
  have hdiff : U - L = X / (20 * h) := by dsimp [L, U]; ring
  have hwide : 2 ≤ U - L := by
    rw [hdiff]
    apply (le_div_iff₀ (by positivity : 0 < 20 * h)).mpr
    linarith
  have hlu : l ≤ u + 1 := by
    exact_mod_cast (show (l : ℝ) ≤ (u : ℝ) + 1 by linarith)
  have hhalf : X / (40 * h) = (U - L) / 2 := by dsimp [L, U]; ring
  change X / (40 * h) ≤ ((Finset.Icc l u).card : ℝ)
  rw [Nat.card_Icc, Nat.cast_sub hlu, Nat.cast_add, Nat.cast_one, hhalf]
  linarith

/-- A constant reciprocal-log mass per window. Coordinate independence,
prime density and asymptotic integration are not inputs to this bound. -/
theorem logGridWindow_reciprocal_lower (X h : ℝ) (hh : 0 < h) (hlarge : 40 * h ≤ X) :
    1 / (42 * h) ≤ ∑ j ∈ logGridWindow X h, 1 / ((j : ℝ) * h) := by
  have hX : 0 < X := by linarith
  have hc := logGridWindow_card_lower X h hh hlarge
  have hp : 0 < (21 / 20 : ℝ) * X := by positivity
  calc
    _ = (X / (40 * h)) / ((21 / 20 : ℝ) * X) := by field_simp; ring
    _ ≤ ((logGridWindow X h).card : ℝ) / ((21 / 20 : ℝ) * X) :=
      div_le_div_of_nonneg_right hc hp.le
    _ = ∑ _j ∈ logGridWindow X h, 1 / ((21 / 20 : ℝ) * X) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
      one_div_le_one_div_of_le (hX.trans_le ((mem_logGridWindow X h hX.le hh j).mp hj).1)
        ((mem_logGridWindow X h hX.le hh j).mp hj).2

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.logGridWindow
#print axioms BinaryFormMoat.GeometryIntegration.mem_logGridWindow
#print axioms BinaryFormMoat.GeometryIntegration.logGridWindow_card_lower
#print axioms BinaryFormMoat.GeometryIntegration.logGridWindow_reciprocal_lower
