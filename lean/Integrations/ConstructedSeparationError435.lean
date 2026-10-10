import Integrations.ConstructedSubsetBudget435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open HarperIntegration

theorem scaledSeparationTarget_mul_log_ge_area (A H L g : ℝ)
    (hH : 0 ≤ H) (hL : 0 < L) (hg : 0 ≤ g) (hg2 : g < 1 / 2) :
    A ≤ (scaledSeparationTarget A H L g : ℝ) * L := by
  have hp : 0 < (1 - 2 * g) * L := mul_pos (by linarith) hL
  have hc := (div_le_iff₀ hp).mp (Nat.le_ceil ((A + H) / ((1 - 2 * g) * L)))
  have hr0 : 0 ≤ (scaledSeparationTarget A H L g : ℝ) * L := by positivity
  have hm := mul_le_of_le_one_left hr0 (show 1 - 2 * g ≤ 1 by linarith)
  change A + H ≤ (scaledSeparationTarget A H L g : ℝ) * ((1 - 2 * g) * L) at hc
  nlinarith

theorem roundedSubsetFailureBound_nonneg (P : Finset ℕ) (d r : ℕ) (η g : ℝ) :
    0 ≤ roundedSubsetFailureBound P d r η g := by
  unfold roundedSubsetFailureBound
  exact add_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (Real.exp_pos _).le

/-- Turn explicit polynomial/logarithmic size conditions into the required small
failure quota. No tail probability bound is supplied as a hypothesis. -/
theorem separation_two_tails_le (d r s : ℕ) (hd : 1 ≤ d) (hr : 0 < r) (hrs : r ≤ s)
    (L g : ℝ) (hL : 0 < L) (hg : 0 < g)
    (hprime : 2 * (Real.log 2) ^ 2 ≤ g ^ 3 * r * L ^ 2)
    (hroot : 1049760 * d * Real.log (2 / g) ≤ g ^ 8 * r) :
    (Real.log 2) ^ 2 / (g ^ 2 * s * L ^ 2) +
      Real.exp (-(g ^ 8 * r) / (1049760 * d)) ≤ g := by
  have hs : 0 < s := hr.trans_le hrs
  have hden : 0 < g ^ 2 * s * L ^ 2 := by positivity
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hm := mul_le_mul_of_nonneg_left hrsR (show 0 ≤ g ^ 3 * L ^ 2 by positivity)
  have hα : (Real.log 2) ^ 2 / (g ^ 2 * s * L ^ 2) ≤ g / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hrate : Real.log (2 / g) ≤ (g ^ 8 * r) / (1049760 * d) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1049760 * d)).mpr
    nlinarith [hroot]
  have hlog : -Real.log (2 / g) = Real.log (g / 2) := by
    rw [Real.log_div (by norm_num) hg.ne', Real.log_div hg.ne' (by norm_num)]
    ring
  have hβ : Real.exp (-(g ^ 8 * r) / (1049760 * d)) ≤ g / 2 := by
    calc
      _ ≤ Real.exp (-Real.log (2 / g)) :=
        Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hrate)
      _ = g / 2 := by rw [hlog, Real.exp_log (by positivity)]
  linarith

/-- Express both tail quotas in the area scale A, eliminating the constructed
integer count from the asymptotic size inputs. -/
theorem constructed_subset_failure_le (P : Finset ℕ) (d : ℕ) (hd : 1 ≤ d)
    (A H g : ℝ) (hA : 0 < A) (hH : 0 ≤ H) (hL : 0 < primeBatchLogMean P)
    (hg : 0 < g) (hg2 : g < 1 / 2)
    (hprime : 2 * (Real.log 2) ^ 2 ≤ g ^ 3 * A * primeBatchLogMean P)
    (hroot : 1049760 * d * primeBatchLogMean P * Real.log (2 / g) ≤ g ^ 8 * A) :
    roundedSubsetFailureBound P d (scaledSeparationTarget A H (primeBatchLogMean P) g) g g ≤ g := by
  let L := primeBatchLogMean P
  let r := scaledSeparationTarget A H L g
  have hr : 0 < r := scaledSeparationTarget_pos A H L g hA hH hL hg2
  have hAr : A ≤ (r : ℝ) * L := scaledSeparationTarget_mul_log_ge_area A H L g hH hL hg.le hg2
  have hq : 0 < harperQuotaWidth g := by
    have h := (harperQuotaWidth_schedule g hg).1
    omega
  have hp : 2 * (Real.log 2) ^ 2 ≤ g ^ 3 * r * L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hAr (show 0 ≤ g ^ 3 * L by positivity)
    nlinarith
  have hb : 1049760 * d * Real.log (2 / g) ≤ g ^ 8 * r := by
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      _ = 1049760 * d * L * Real.log (2 / g) := by ring
      _ ≤ g ^ 8 * A := hroot
      _ ≤ g ^ 8 * ((r : ℝ) * L) := mul_le_mul_of_nonneg_left hAr (by positivity)
      _ = _ := by ring
  exact separation_two_tails_le d r (roundedHarperCount (harperQuotaWidth g) r) hd hr
    (roundedHarperCount_bounds _ r hq).1 L g hL hg hp hb

/-- One fixed-power size condition supplies rounding and both tail quotas.
The coarse log(x)<=x bound avoids a separate logarithmic asymptotic argument. -/
theorem separation_power_nine_quotas (d : ℕ) (A L g : ℝ) (hA : 0 ≤ A)
    (hL : 0 < L) (hL2 : Real.log 2 ≤ L) (hg : 0 < g) (hg1 : g ≤ 1)
    (hsize : (19 + 2099520 * d) * L ≤ g ^ 9 * A) :
    (1 + 18 / g ^ 2) * L ≤ g * A ∧
      2 * (Real.log 2) ^ 2 ≤ g ^ 3 * A * L ∧
      1049760 * d * L * Real.log (2 / g) ≤ g ^ 8 * A := by
  have h6 : g ^ 6 ≤ 1 := pow_le_one₀ hg.le hg1
  have h93 : g ^ 9 ≤ g ^ 3 := by
    calc
      _ = g ^ 3 * g ^ 6 := by ring
      _ ≤ g ^ 3 * 1 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = _ := mul_one _
  have h19 : 19 * L ≤ g ^ 9 * A := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [mul_nonneg hd0 hL.le]
  have h3 : 19 * L ≤ g ^ 3 * A := h19.trans (mul_le_mul_of_nonneg_right h93 hA)
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hround : (1 + 18 / g ^ 2) * L ≤ g * A := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hg)).mp
    calc
      _ = (g ^ 2 + 18) * L := by field_simp
      _ ≤ 19 * L := mul_le_mul_of_nonneg_right (by linarith) hL.le
      _ ≤ g ^ 3 * A := h3
      _ = _ := by ring
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq := mul_nonneg (sub_nonneg.mpr hL2) (add_nonneg hL.le hlog2)
  have hp := mul_le_mul_of_nonneg_right h3 hL.le
  have hprime : 2 * (Real.log 2) ^ 2 ≤ g ^ 3 * A * L := by nlinarith
  have hlog : Real.log (2 / g) ≤ 2 / g := Real.log_le_self (by positivity)
  have hroot : 1049760 * d * L * Real.log (2 / g) ≤ g ^ 8 * A := by
    apply (mul_le_mul_iff_left₀ hg).mp
    calc
      _ ≤ (1049760 * d * L * (2 / g)) * g := by gcongr
      _ = 2099520 * d * L := by field_simp; ring
      _ ≤ g ^ 9 * A := by nlinarith
      _ = _ := by ring
  exact ⟨hround, hprime, hroot⟩

/-- Derive a concrete (1-8g)L geometric floor, including both failure and prefix
costs. There is no assumed entropy floor or normalized geometric inequality. -/
theorem scalar_coordinate_floor_ge (A C B L g ε : ℝ) (s : ℕ)
    (hA : 0 < A) (hC : 0 ≤ C) (hs : 0 < s)
    (hg8 : g ≤ 1 / 8) (hε0 : 0 ≤ ε) (hε : ε ≤ g)
    (hcount : (s : ℝ) * L ≤ (1 + 6 * g) * A) (hcost : C + B ≤ g * A) :
    (1 - 8 * g) * L ≤ ((1 - ε) * (A - C) - B) / s := by
  have hθ : 0 ≤ 1 - 8 * g := by linarith
  have hm := mul_le_mul_of_nonneg_left hcount hθ
  have hf : (1 - 8 * g) * (1 + 6 * g) ≤ 1 - 2 * g := by nlinarith [sq_nonneg g]
  have hfA := mul_le_mul_of_nonneg_right hf hA.le
  have hεA := mul_le_mul_of_nonneg_right hε hA.le
  have hεC := mul_nonneg hε0 hC
  have hnum : (1 - 2 * g) * A ≤ (1 - ε) * (A - C) - B := by nlinarith
  apply (le_div_iff₀ (by exact_mod_cast hs : (0 : ℝ) < s)).mpr
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.scaledSeparationTarget_mul_log_ge_area
#print axioms BinaryFormMoat.GeometryIntegration.roundedSubsetFailureBound_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.separation_two_tails_le
#print axioms BinaryFormMoat.GeometryIntegration.constructed_subset_failure_le
#print axioms BinaryFormMoat.GeometryIntegration.separation_power_nine_quotas
#print axioms BinaryFormMoat.GeometryIntegration.scalar_coordinate_floor_ge
