import Integrations.RoundedHarperQuota435

noncomputable section
namespace BinaryFormMoat.HarperIntegration

/-- Work backwards from the required log-product gap, then round to a Harper block. -/
def scaledSeparationTarget (A H L g : ℝ) : ℕ := ⌈(A + H) / ((1 - 2 * g) * L)⌉₊

theorem scaledSeparationTarget_pos (A H L g : ℝ) (hA : 0 < A) (hH : 0 ≤ H)
    (hL : 0 < L) (hg : g < 1 / 2) : 0 < scaledSeparationTarget A H L g := by
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (by linarith) (mul_pos (by linarith) hL)

/-- The rounded count meets the lower log budget, with no assumed count inequality. -/
theorem scaledSeparationCount_log_lower (q : ℕ) (hq : 0 < q)
    (A H L g : ℝ) (hL : 0 < L) (hg : g < 1 / 2) :
    A + H ≤ (1 - 2 * g) * roundedHarperCount q (scaledSeparationTarget A H L g) * L := by
  have hp : 0 < (1 - 2 * g) * L := mul_pos (by linarith) hL
  have hc := (div_le_iff₀ hp).mp (Nat.le_ceil ((A + H) / ((1 - 2 * g) * L)))
  have hr : (scaledSeparationTarget A H L g : ℝ) ≤
      roundedHarperCount q (scaledSeparationTarget A H L g) := by
    exact_mod_cast (roundedHarperCount_bounds q _ hq).1
  calc
    A + H ≤ (scaledSeparationTarget A H L g : ℝ) * ((1 - 2 * g) * L) := hc
    _ ≤ (roundedHarperCount q (scaledSeparationTarget A H L g) : ℝ) * ((1 - 2 * g) * L) :=
      mul_le_mul_of_nonneg_right hr hp.le
    _ = _ := by ring

theorem scaledSeparationCount_log_upper (q : ℕ) (hq : 0 < q)
    (A H L g : ℝ) (hA : 0 ≤ A + H) (hL : 0 < L) (hg : g < 1 / 2) :
    (1 - 2 * g) * roundedHarperCount q (scaledSeparationTarget A H L g) * L ≤
      A + H + (1 - 2 * g) * (1 + 2 * q) * L := by
  have hp : 0 < (1 - 2 * g) * L := mul_pos (by linarith) hL
  have ht := Nat.ceil_lt_add_one (div_nonneg hA hp.le)
  have hr : (roundedHarperCount q (scaledSeparationTarget A H L g) : ℝ) <
      scaledSeparationTarget A H L g + 2 * q := by
    exact_mod_cast (roundedHarperCount_bounds q _ hq).2
  have ht' : (scaledSeparationTarget A H L g : ℝ) + 2 * q <
      ((A + H) / ((1 - 2 * g) * L) + 1) + 2 * q := by
    simpa only [scaledSeparationTarget, add_comm] using add_lt_add_right ht (2 * q)
  have hm := mul_lt_mul_of_pos_right (hr.trans ht') hp
  rw [add_mul, add_mul, div_mul_cancel₀ _ hp.ne'] at hm
  nlinarith

/-- Small overhead and one-block rounding cost keep the geometric log density near one. -/
theorem scaledSeparationCount_density_upper (q : ℕ) (hq : 0 < q)
    (A H L g : ℝ) (hA : 0 < A) (hH : 0 ≤ H) (hL : 0 < L)
    (hg : 0 ≤ g) (hg8 : g ≤ 1 / 8) (hsmall : H ≤ g * A)
    (hround : (1 + 2 * q) * L ≤ g * A) :
    (roundedHarperCount q (scaledSeparationTarget A H L g) : ℝ) * L ≤ (1 + 6 * g) * A := by
  have hp : 0 < 1 - 2 * g := by linarith
  have hu := scaledSeparationCount_log_upper q hq A H L g (by linarith) hL (by linarith)
  have hm := mul_le_mul_of_nonneg_left hround hp.le
  have hf : (1 + 2 * g) * A ≤ (1 - 2 * g) * ((1 + 6 * g) * A) := by
    have hgA : 0 ≤ g * A := mul_nonneg hg hA.le
    have h := mul_nonneg (show 0 ≤ 2 - 12 * g by linarith) hgA
    nlinarith
  have ht : (1 - 2 * g) *
      ((roundedHarperCount q (scaledSeparationTarget A H L g) : ℝ) * L) ≤
        (1 - 2 * g) * ((1 + 6 * g) * A) := by
    have hh : (1 - 2 * g) * (g * A) ≤ g * A := by
      exact mul_le_of_le_one_left (mul_nonneg hg hA.le) (by linarith)
    nlinarith
  nlinarith

theorem scaledSeparationCount_fits (q b available : ℕ) (hq : 0 < q)
    (A H L g : ℝ) (hinventory : b + scaledSeparationTarget A H L g + 2 * q ≤ available) :
    b + roundedHarperCount q (scaledSeparationTarget A H L g) ≤ available := by
  have h := (roundedHarperCount_bounds q (scaledSeparationTarget A H L g) hq).2
  omega

/-- Replace the integer width cost by its explicit eta^-2 envelope. -/
theorem harperQuota_rounding_cost (η L B : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 0 ≤ L) (hbudget : (1 + 18 / η ^ 2) * L ≤ B) :
    (1 + 2 * harperQuotaWidth η) * L ≤ B := by
  have hq := harperQuotaWidth_le η hη hη1
  calc
    _ ≤ (1 + 2 * (9 / η ^ 2)) * L := by gcongr
    _ = (1 + 18 / η ^ 2) * L := by ring
    _ ≤ B := hbudget

end BinaryFormMoat.HarperIntegration

#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationTarget
#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationTarget_pos
#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationCount_log_lower
#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationCount_log_upper
#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationCount_density_upper
#print axioms BinaryFormMoat.HarperIntegration.scaledSeparationCount_fits
#print axioms BinaryFormMoat.HarperIntegration.harperQuota_rounding_cost
