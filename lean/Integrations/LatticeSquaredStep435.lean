import Integrations.FiniteSieveExit435

namespace BinaryFormMoat.FiniteSieveIntegration

/-- A coarse integral conversion suffices for existence of a moat. It
avoids square roots and introduces no geometric optimization premise. -/
theorem sqDist_le_of_latticeDist_le (D : ℕ) (x y : Point) (h : latticeDist x y ≤ D) :
    sqDist x y ≤ (2 * D ^ 2 : ℕ) := by
  have hxN : (x.1 - y.1).natAbs ≤ D := by dsimp [latticeDist] at h; omega
  have hyN : (x.2 - y.2).natAbs ≤ D := by dsimp [latticeDist] at h; omega
  have hx : |x.1 - y.1| ≤ (D : ℤ) := by
    simpa only [Int.natCast_natAbs] using
      (show (((x.1 - y.1).natAbs : ℕ) : ℤ) ≤ D by exact_mod_cast hxN)
  have hy : |x.2 - y.2| ≤ (D : ℤ) := by
    simpa only [Int.natCast_natAbs] using
      (show (((x.2 - y.2).natAbs : ℕ) : ℤ) ≤ D by exact_mod_cast hyN)
  have hsx := (sq_le_sq₀ (abs_nonneg (x.1 - y.1)) (Nat.cast_nonneg D)).mpr hx
  have hsy := (sq_le_sq₀ (abs_nonneg (x.2 - y.2)) (Nat.cast_nonneg D)).mpr hy
  simp only [sq_abs] at hsx hsy
  dsimp only [sqDist]
  push_cast
  linarith

end BinaryFormMoat.FiniteSieveIntegration
#print axioms BinaryFormMoat.FiniteSieveIntegration.sqDist_le_of_latticeDist_le
