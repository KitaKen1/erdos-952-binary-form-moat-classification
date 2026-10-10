import Moat.FiniteSetPacking

namespace BinaryFormMoat

noncomputable def rotatedX (a b : ℝ) (z : Point) : ℝ := a * z.1 + b * z.2

noncomputable def rotatedY (a b : ℝ) (z : Point) : ℝ := -b * z.1 + a * z.2

noncomputable def rotatedRectanglePoints (a b : ℝ) (A B : ℕ) : Finset Point := by
  classical
  exact (rectanglePoints (A + B) (A + B)).filter fun z =>
    |rotatedX a b z| ≤ (A : ℝ) ∧ |rotatedY a b z| ≤ (B : ℝ)

theorem rotation_coeff_abs_le_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    |a| ≤ 1 ∧ |b| ≤ 1 := by
  exact ⟨(sq_le_one_iff_abs_le_one a).mp (by nlinarith [sq_nonneg b]),
    (sq_le_one_iff_abs_le_one b).mp (by nlinarith [sq_nonneg a])⟩

theorem rotated_coordinates_inverse (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (z : Point) :
    (z.1 : ℝ) = a * rotatedX a b z - b * rotatedY a b z ∧
    (z.2 : ℝ) = b * rotatedX a b z + a * rotatedY a b z := by
  constructor
  · calc
      (z.1 : ℝ) = (a ^ 2 + b ^ 2) * (z.1 : ℝ) := by rw [hab, one_mul]
      _ = a * rotatedX a b z - b * rotatedY a b z := by
        simp only [rotatedX, rotatedY]; ring
  · calc
      (z.2 : ℝ) = (a ^ 2 + b ^ 2) * (z.2 : ℝ) := by rw [hab, one_mul]
      _ = b * rotatedX a b z + a * rotatedY a b z := by
        simp only [rotatedX, rotatedY]; ring

theorem rotated_rectangle_coordinate_bound (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (A B : ℕ) (z : Point) (hx : |rotatedX a b z| ≤ (A : ℝ))
    (hy : |rotatedY a b z| ≤ (B : ℝ)) :
    z.1.natAbs ≤ A + B ∧ z.2.natAbs ≤ A + B := by
  obtain ⟨ha, hb⟩ := rotation_coeff_abs_le_one a b hab
  obtain ⟨hzx, hzy⟩ := rotated_coordinates_inverse a b hab z
  have hfirst : |(z.1 : ℝ)| ≤ (A : ℝ) + B := by
    rw [hzx]
    calc
      |a * rotatedX a b z - b * rotatedY a b z| ≤
          |a * rotatedX a b z| + |b * rotatedY a b z| := abs_sub _ _
      _ = |a| * |rotatedX a b z| + |b| * |rotatedY a b z| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * A + 1 * B := add_le_add
        (mul_le_mul ha hx (abs_nonneg _) (by norm_num))
        (mul_le_mul hb hy (abs_nonneg _) (by norm_num))
      _ = (A : ℝ) + B := by ring
  have hsecond : |(z.2 : ℝ)| ≤ (A : ℝ) + B := by
    rw [hzy]
    calc
      |b * rotatedX a b z + a * rotatedY a b z| ≤
          |b * rotatedX a b z| + |a * rotatedY a b z| := abs_add_le _ _
      _ = |b| * |rotatedX a b z| + |a| * |rotatedY a b z| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * A + 1 * B := add_le_add
        (mul_le_mul hb hx (abs_nonneg _) (by norm_num))
        (mul_le_mul ha hy (abs_nonneg _) (by norm_num))
      _ = (A : ℝ) + B := by ring
  rw [← Int.cast_abs, ← Nat.cast_natAbs] at hfirst hsecond
  constructor
  · exact_mod_cast hfirst
  · exact_mod_cast hsecond

theorem mem_rotatedRectanglePoints (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (A B : ℕ) (z : Point) :
    z ∈ rotatedRectanglePoints a b A B ↔
      |rotatedX a b z| ≤ (A : ℝ) ∧ |rotatedY a b z| ≤ (B : ℝ) := by
  classical
  simp only [rotatedRectanglePoints, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h =>
    ⟨(mem_rectanglePoints z _ _).mpr
      (rotated_rectangle_coordinate_bound a b hab A B z h.1 h.2), h⟩⟩

theorem rotatedRectangle_radius (a b : ℝ) (A B : ℕ) :
    ∀ z ∈ rotatedRectanglePoints a b A B, max z.1.natAbs z.2.natAbs ≤ A + B := by
  classical
  intro z hz
  exact max_le ((mem_rectanglePoints z _ _).mp (Finset.mem_filter.mp hz).1).1
    ((mem_rectanglePoints z _ _).mp (Finset.mem_filter.mp hz).1).2

theorem determinant_rotation_identity (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (z w : Point) :
    rotatedX a b z * rotatedY a b w - rotatedY a b z * rotatedX a b w =
      (determinant z w : ℝ) := by
  calc
    _ = (a ^ 2 + b ^ 2) * ((z.1 : ℝ) * w.2 - (z.2 : ℝ) * w.1) := by
      simp only [rotatedX, rotatedY]; ring
    _ = (determinant z w : ℝ) := by simp [hab, determinant]

/-- The bound is the product of the two widths, even for a rotated thin rectangle. -/
theorem rotatedRectangle_determinant_bound (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (A B : ℕ) :
    ∀ z ∈ rotatedRectanglePoints a b A B, ∀ w ∈ rotatedRectanglePoints a b A B,
      (determinant z w).natAbs ≤ 2 * A * B := by
  intro z hz w hw
  obtain ⟨hzx, hzy⟩ := (mem_rotatedRectanglePoints a b hab A B z).mp hz
  obtain ⟨hwx, hwy⟩ := (mem_rotatedRectanglePoints a b hab A B w).mp hw
  have hreal : |(determinant z w : ℝ)| ≤ 2 * (A : ℝ) * B := by
    rw [← determinant_rotation_identity a b hab]
    calc
      _ ≤ |rotatedX a b z * rotatedY a b w| +
          |rotatedY a b z * rotatedX a b w| := abs_sub _ _
      _ = |rotatedX a b z| * |rotatedY a b w| +
          |rotatedY a b z| * |rotatedX a b w| := by rw [abs_mul, abs_mul]
      _ ≤ (A : ℝ) * B + (B : ℝ) * A := add_le_add
        (mul_le_mul hzx hwy (abs_nonneg _) (Nat.cast_nonneg _))
        (mul_le_mul hzy hwx (abs_nonneg _) (Nat.cast_nonneg _))
      _ = 2 * (A : ℝ) * B := by ring
  rw [← Int.cast_abs, ← Nat.cast_natAbs] at hreal
  exact_mod_cast hreal

end BinaryFormMoat
