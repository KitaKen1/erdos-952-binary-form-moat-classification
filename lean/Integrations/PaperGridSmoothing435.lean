import Integrations.PaperLogGridBudget435
import Integrations.WalkWordBudget435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration

/-- The number of actual used batches is bounded by the exact finite
truncation, regardless of how many disjoint paper windows are selected. -/
theorem paperGeometricIndices_card_le_ceil (d M B : ℕ) :
    (paperGeometricIndices d M B).card ≤
      ⌈((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B⌉₊ + 1 := by
  unfold paperGeometricIndices
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

theorem paperGeometricIndices_card_upper (d M B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    ((paperGeometricIndices d M B).card : ℝ) ≤
      Real.log (paperScheduleMaxT d M) / Real.log B + 2 := by
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hx := (paperScheduleX_pos d M hd).le
  have hceil := Nat.ceil_lt_add_one
    (by positivity : 0 ≤ ((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B)
  have hc : ((paperGeometricIndices d M B).card : ℝ) ≤
      (⌈((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B⌉₊ : ℝ) + 1 := by
    exact_mod_cast paperGeometricIndices_card_le_ceil d M B
  simp only [paperScheduleMaxT, Real.log_exp]
  linarith

/-- A scalar envelope for the ALREADY proved normalized common-law word
budget, using the actual number of grid batches. -/
def paperGridSmoothingError (d M B : ℕ) (K : ℝ) : ℝ :=
  ((paperGeometricIndices d M B).card : ℝ) *
    ((1 + 9 * Real.log (paperScheduleMaxT d M) + K) / (paperScheduleMaxT d M) ^ 9)

theorem paperGridSmoothingError_nonneg (d M B : ℕ) (hd : 1 ≤ d) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ paperGridSmoothingError d M B K := by
  have hx := (paperScheduleX_pos d M hd).le
  simp only [paperGridSmoothingError, paperScheduleMaxT, Real.log_exp]
  positivity

/-- The actual batch-count times the normalized smoothing error tends to
zero. This uses x^2/exp(9x), rather than a new residue-alphabet continuity
estimate; the checked conditional-word coupling cost needs only log(K). -/
theorem tendsto_paperGridSmoothingError (d B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B)
    (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun M => paperGridSmoothingError d M B K) atTop (𝓝 0) := by
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  let C := 1 / Real.log B + 2
  let D := C * (10 + K)
  have hx : Tendsto (fun M => (21 / 20 : ℝ) * paperScheduleX d M) atTop atTop :=
    (tendsto_paperScheduleX d hd).const_mul_atTop (by norm_num)
  have hz : Tendsto (fun x : ℝ => D * x ^ 2 / Real.exp (9 * x)) atTop (𝓝 0) := by
    convert ((isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 9)).tendsto_div_nhds_zero).const_mul D using 1
    · ext x; ring
    · ring
  have hu : ∀ᶠ M : ℕ in atTop, paperGridSmoothingError d M B K ≤
      D * ((21 / 20 : ℝ) * paperScheduleX d M) ^ 2 /
        Real.exp (9 * ((21 / 20 : ℝ) * paperScheduleX d M)) := by
    filter_upwards [hx.eventually_ge_atTop 1] with M hM
    let x := (21 / 20 : ℝ) * paperScheduleX d M
    have hx1 : 1 ≤ x := hM
    have hc := paperGeometricIndices_card_upper d M B hd hB
    simp only [paperScheduleMaxT, Real.log_exp] at hc
    have hcx : ((paperGeometricIndices d M B).card : ℝ) ≤ C * x := by
      have h := hc.trans (add_le_add_right (by linarith : (2 : ℝ) ≤ 2 * x) (x / Real.log B))
      convert h using 1; dsimp [C, x]; ring
    have hnum : 1 + 9 * x + K ≤ (10 + K) * x := by
      nlinarith [mul_nonneg hK (sub_nonneg.mpr hx1)]
    have hprod : ((paperGeometricIndices d M B).card : ℝ) * (1 + 9 * x + K) ≤ D * x ^ 2 := by
      have h := mul_le_mul hcx hnum (by positivity : 0 ≤ 1 + 9 * x + K) (by dsimp [C]; positivity)
      convert h using 1; dsimp [D]; ring
    unfold paperGridSmoothingError paperScheduleMaxT
    rw [Real.log_exp, ← Real.exp_nat_mul]
    change _ * ((1 + 9 * x + K) / Real.exp (9 * x)) ≤ _
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hprod (Real.exp_pos _).le
  exact squeeze_zero' (Eventually.of_forall fun M => paperGridSmoothingError_nonneg d M B hd K hK)
    hu (hz.comp hx)

/-- The numeric end of the sieve contradiction, with an explicit boundary:
the actual information lower-rate/upper-budget inequality must still be
derived from the walk before this theorem excludes it. -/
theorem paperGrid_information_budget_eventually_impossible (d B : ℕ)
    (hd : 1 ≤ d) (hB : 3 ≤ B) (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∀ᶠ M : ℕ in atTop, ¬ c * paperGeometricLogBudget d M B ≤
      K + paperGridSmoothingError d M B K := by
  have hg := (tendsto_paperGeometricLogBudget d B hd hB).const_mul_atTop hc
  have he := tendsto_paperGridSmoothingError d B hd hB K hK
  filter_upwards [hg.eventually_gt_atTop (K + 1), he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with M hM hE
  linarith

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_card_le_ceil
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_card_upper
#print axioms BinaryFormMoat.GeometryIntegration.paperGridSmoothingError
#print axioms BinaryFormMoat.GeometryIntegration.paperGridSmoothingError_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperGridSmoothingError
#print axioms BinaryFormMoat.GeometryIntegration.paperGrid_information_budget_eventually_impossible
