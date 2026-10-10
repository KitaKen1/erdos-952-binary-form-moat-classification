import Moat.DyadicLineTail

namespace BinaryFormMoat

/-- A lower bound on every prime gives the corresponding product bound. -/
theorem dyadic_prime_product_lower (P : Finset ℕ) (T : ℕ)
    (hlo : ∀ p ∈ P, T ≤ p) : T ^ P.card ≤ ∏ p ∈ P, p := by
  calc
    _ = ∏ _p ∈ P, T := by simp
    _ ≤ _ := Finset.prod_le_prod fun p hp => hlo p hp

theorem dyadic_prime_log_sum_lower (P : Finset ℕ) (T : ℕ) (hT : 0 < T)
    (hlo : ∀ p ∈ P, T ≤ p) :
    (P.card : ℝ) * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
  calc
    _ = ∑ _p ∈ P, Real.log (T : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun p hp =>
      Real.log_le_log (by exact_mod_cast hT) (by exact_mod_cast hlo p hp)

/-- The root-tail gap follows from a size budget and the lower end of the
dyadic interval, with the coefficient cost included in C. -/
theorem rectangle_log_gap_of_dyadic_lower (P : Finset ℕ) (T : ℕ) (hT : 0 < T)
    (hlo : ∀ p ∈ P, T ≤ p) (C η : ℝ)
    (hsize : C ≤ (1 - η) * P.card * Real.log (T : ℝ)) :
    C + η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
  have h := dyadic_prime_log_sum_lower P T hT hlo
  nlinarith only [h, hsize]

/-- For k=2*q*l and q>=2, a coarse area budget discharges the determinant
separation condition. The estimate 2*T<=T^2 avoids logarithmic rounding. -/
theorem rectangle_separation_of_dyadic_bounds (P : Finset ℕ) (T q l A B : ℕ)
    (hT : 2 ≤ T) (hq : 2 ≤ q) (hcount : P.card = 2 * q * l)
    (hlo : ∀ p ∈ P, T ≤ p) (harea : 2 * A * B < T ^ ((2 * q - 4) * l)) :
    (2 * A * B) * (2 * T) ^ (2 * l) < ∏ p ∈ P, p := by
  have hbase : 2 * T ≤ T ^ 2 := by nlinarith
  have hpow : (2 * T) ^ (2 * l) ≤ T ^ (4 * l) := by
    calc
      _ ≤ (T ^ 2) ^ (2 * l) := Nat.pow_le_pow_left hbase _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hexp : (2 * q - 4) * l + 4 * l = 2 * q * l := by
    have h : (2 * q - 4) + 4 = 2 * q := Nat.sub_add_cancel (by omega)
    calc
      _ = ((2 * q - 4) + 4) * l := by ring
      _ = _ := by rw [h]
  calc
    _ ≤ (2 * A * B) * T ^ (4 * l) := Nat.mul_le_mul_left _ hpow
    _ < T ^ ((2 * q - 4) * l) * T ^ (4 * l) :=
      Nat.mul_lt_mul_of_pos_right harea (pow_pos (by omega) _)
    _ = T ^ (2 * q * l) := by rw [← pow_add, hexp]
    _ ≤ _ := by simpa only [hcount] using dyadic_prime_product_lower P T hlo

/-- Convert a logarithmic radius bound to an integral power bound. Radius zero
is handled separately, since Lean's logarithm is also defined at zero. -/
theorem nat_le_pow_of_log_le (R T k : ℕ) (hT : 0 < T)
    (hlog : Real.log (R : ℝ) ≤ (k : ℝ) * Real.log (T : ℝ)) : R ≤ T ^ k := by
  by_cases hR : R = 0
  · simp [hR]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hpow : Real.log ((T : ℝ) ^ k) = (k : ℝ) * Real.log (T : ℝ) := Real.log_pow _ _
  rw [← hpow] at hlog
  exact_mod_cast (Real.log_le_log_iff hRpos (pow_pos hTpos k)).mp hlog

/-- In the concrete q=12 schedule, the radius budget already implies the
area budget. This removes a separate arithmetic condition from the adapter. -/
theorem rectangle_area_of_radius_log (A B T l : ℕ) (hT : 2 ≤ T) (hl : 1 ≤ l)
    (hlog : Real.log ((max A B : ℕ) : ℝ) ≤ 6 * l * Real.log (T : ℝ)) :
    2 * A * B < T ^ (20 * l) := by
  have hR : max A B ≤ T ^ (6 * l) :=
    nat_le_pow_of_log_le (max A B) T (6 * l) (by omega) (by simpa using hlog)
  have hA : A ≤ T ^ (6 * l) := (le_max_left _ _).trans hR
  have hB : B ≤ T ^ (6 * l) := (le_max_right _ _).trans hR
  calc
    _ ≤ 2 * T ^ (6 * l) * T ^ (6 * l) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hB
    _ = 2 * T ^ (12 * l) := by rw [mul_assoc, ← pow_add]; congr 1; ring
    _ ≤ T * T ^ (12 * l) := Nat.mul_le_mul_right _ hT
    _ = T ^ (12 * l + 1) := by rw [pow_succ, mul_comm]
    _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)

end BinaryFormMoat
