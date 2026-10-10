import Integrations.EmpiricalTail435
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def rareSampleSize (p : ℕ) (β : ℝ) : ℕ :=
  Nat.ceil ((p : ℝ) ^ (1 - β))

noncomputable def smallListCutoff (p : ℕ) (β : ℝ) : ℕ :=
  Nat.floor ((p : ℝ) ^ (1 - β / 2))

theorem rareSampleSize_pos (p : ℕ) (hp : 0 < p) (β : ℝ) : 0 < rareSampleSize p β := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp) _

theorem rareSampleSize_le (p : ℕ) (hp : 1 ≤ p) (β : ℝ) (hβ : 0 ≤ β) :
    rareSampleSize p β ≤ p := by
  apply Nat.ceil_le.mpr
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp)
    (by linarith : 1 - β ≤ (1 : ℝ))).trans_eq (Real.rpow_one _)

theorem rareSampleSize_scale (p : ℕ) (hp : 0 < p) (β : ℝ) :
    (p : ℝ) ^ (-β) ≤ (rareSampleSize p β : ℝ) / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ = (p : ℝ) ^ (1 - β) / p := by
      rw [← Real.rpow_sub_one hp'.ne']
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (Nat.le_ceil _) hp'.le

theorem exists_rare_sample {G : Type*} [Fintype G] (E : Finset G) (β : ℝ)
    (hdeficient : (Fintype.card G : ℝ) ^ (1 - β) ≤ E.card) :
    ∃ K ⊆ E, K.card = rareSampleSize (Fintype.card G) β := by
  exact Finset.exists_subset_card_eq (Nat.ceil_le.mpr hdeficient)

theorem smallListCutoff_pos (p : ℕ) (hp : 1 ≤ p) (β : ℝ) (hβ : β ≤ 2) :
    1 ≤ smallListCutoff p β := by
  unfold smallListCutoff
  apply Nat.le_floor
  simpa only [Nat.cast_one] using Real.one_le_rpow
    (show (1 : ℝ) ≤ p by exact_mod_cast hp) (show 0 ≤ 1 - β / 2 by linarith)

/-- Flooring the list cutoff pays no extra log(2) in the source gap. -/
theorem smallListCutoff_log_gap (p : ℕ) (hp : 1 ≤ p) (β : ℝ) (hβ : β ≤ 2) :
    β / 2 * Real.log p ≤ Real.log p - Real.log (smallListCutoff p β : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hM : (0 : ℝ) < smallListCutoff p β := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (smallListCutoff_pos p hp β hβ))
  have h := Real.log_le_log hM
    (Nat.floor_le (Real.rpow_pos_of_pos hp' (1 - β / 2)).le)
  rw [Real.log_rpow hp'] at h
  linarith only [h]

theorem coverage_exception_size_lt_cutoff (p m : ℕ) (hp : 0 < p) (β δ : ℝ)
    (hδ : 0 < δ) (hsize : (m : ℝ) < (p : ℝ) ^ (1 - β))
    (hmargin : δ⁻¹ < (p : ℝ) ^ (β / 2)) :
    (m : ℝ) / δ < (p : ℝ) ^ (1 - β / 2) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ = (m : ℝ) * δ⁻¹ := div_eq_mul_inv _ _
    _ < (p : ℝ) ^ (1 - β) * δ⁻¹ :=
      mul_lt_mul_of_pos_right hsize (inv_pos.mpr hδ)
    _ < (p : ℝ) ^ (1 - β) * (p : ℝ) ^ (β / 2) :=
      mul_lt_mul_of_pos_left hmargin (Real.rpow_pos_of_pos hp' _)
    _ = _ := by
      rw [← Real.rpow_add hp']
      congr 1
      ring

theorem overlapExceptionalCandidates_card_le_cutoff {G : Type*} [Fintype G]
    [DecidableEq G] [AddGroup G] (K E : Finset G) (hK : K.Nonempty)
    (β δ : ℝ) (hδ : 0 < δ)
    (hsize : (E.card : ℝ) < (Fintype.card G : ℝ) ^ (1 - β))
    (hmargin : δ⁻¹ < (Fintype.card G : ℝ) ^ (β / 2)) :
    (overlapExceptionalCandidates K E δ).card ≤ smallListCutoff (Fintype.card G) β := by
  apply Nat.le_floor
  exact ((overlapExceptionalCandidates_card_le K E hK δ hδ).trans_lt
    (coverage_exception_size_lt_cutoff _ E.card Fintype.card_pos β δ hδ hsize hmargin)).le

theorem coverage_floor_parameter_gap (τ δ : ℝ) (hτ : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) :
    τ + 2 * δ ≤ 1 ∧ τ + 2 * δ ≤ (τ + 4 * δ) * (1 - δ) := by
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_right
      (show τ + 4 * δ ≤ 7 / 16 by linarith) hδ.le
    nlinarith only [h, hδ]

/-- Apply the strict source exception bound to an integer cutoff. Passing
through the integer candidate count avoids rounding E.card/delta upward. -/
theorem empiricalList_size_failure_le_rounded_coverage {Ω ι G : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype G] [DecidableEq G] [AddGroup G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K E : Finset G) (hK : K.Nonempty)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (τ β β' δ : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64)
    (hsize : (E.card : ℝ) < (Fintype.card G : ℝ) ^ (1 - β'))
    (hmargin : δ⁻¹ < (Fintype.card G : ℝ) ^ (β' / 2))
    (hKsize : K.card = rareSampleSize (Fintype.card G) β)
    (hcoverage : ∀ j, ∀ h ∉ E, (τ + 4 * δ) / Fintype.card G ≤
      μ.real ((fun ω => D ω j) ⁻¹' {h})) :
    μ.real {ω | smallListCutoff (Fintype.card G) β' < (empiricalList K
      ((Fintype.card ι : ℝ) * (τ + δ) * ((K.card : ℝ) / Fintype.card G)) (D ω)).card} ≤
      (Fintype.card G : ℝ) *
        Real.exp (-δ ^ 2 * (Fintype.card ι : ℝ) * (Fintype.card G : ℝ) ^ (-β) / 2) := by
  classical
  let B := overlapExceptionalCandidates K E δ
  have hgap := coverage_floor_parameter_gap τ δ hτmax hδ hδmax
  apply empiricalList_size_failure_le_coverage_scale μ K B D hD hI _
    (overlapExceptionalCandidates_card_le_cutoff K E hK β' δ hδ hsize hmargin)
    τ δ ((K.card : ℝ) / Fintype.card G) β hτ hδ
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hgap.1
  · intro x hx j
    have h := hitTrialEvent_probability_floor_of_overlap μ K E x D hD j
      ((τ + 4 * δ) / Fintype.card G) δ (by positivity) (hcoverage j)
      (overlap_le_of_not_exceptional K E δ x hx)
    have hg := mul_le_mul_of_nonneg_right hgap.2
      (div_nonneg (Nat.cast_nonneg K.card) (Nat.cast_nonneg (Fintype.card G)))
    apply hg.trans
    convert h using 1
    ring
  · rw [hKsize]
    exact rareSampleSize_scale _ Fintype.card_pos β

noncomputable def coverageTrialCount (p : ℕ) (β δ ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * (p : ℝ) ^ β / δ ^ 2 * Real.log ((p : ℝ) / ε)))

theorem coverageTrialCount_pos (p : ℕ) (β δ ε : ℝ) :
    1 ≤ coverageTrialCount p β δ ε := le_max_left _ _

/-- A closed formula for enough trials, avoiding an asymptotic existence
argument. The maximum with one also handles nonpositive logarithms. -/
theorem coverageTrialCount_tail (p : ℕ) (hp : 0 < p) (β δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    (p : ℝ) * Real.exp (-δ ^ 2 * (coverageTrialCount p β δ ε : ℝ) *
      (p : ℝ) ^ (-β) / 2) ≤ ε := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpow := Real.rpow_pos_of_pos hp' β
  have hceil : 2 * (p : ℝ) ^ β / δ ^ 2 * Real.log ((p : ℝ) / ε) ≤
      (coverageTrialCount p β δ ε : ℝ) := (Nat.le_ceil _).trans
        (Nat.cast_le.mpr (le_max_right 1 _))
  have hc : 0 ≤ δ ^ 2 * (p : ℝ) ^ (-β) / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hceil hc
  have he : δ ^ 2 * (p : ℝ) ^ (-β) / 2 *
      (2 * (p : ℝ) ^ β / δ ^ 2 * Real.log ((p : ℝ) / ε)) =
      Real.log ((p : ℝ) / ε) := by
    rw [Real.rpow_neg hp'.le]
    field_simp [hδ.ne', hpow.ne']
  rw [he] at hm
  have hexp : Real.exp (-δ ^ 2 * (coverageTrialCount p β δ ε : ℝ) *
      (p : ℝ) ^ (-β) / 2) ≤ Real.exp (-Real.log ((p : ℝ) / ε)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hm]
  have h := mul_le_mul_of_nonneg_left hexp hp'.le
  rw [Real.exp_neg, Real.exp_log (div_pos hp' hε)] at h
  convert h using 1
  field_simp

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.rareSampleSize_pos
#print axioms BinaryFormMoat.EntropyIntegration.rareSampleSize_le
#print axioms BinaryFormMoat.EntropyIntegration.rareSampleSize_scale
#print axioms BinaryFormMoat.EntropyIntegration.exists_rare_sample
#print axioms BinaryFormMoat.EntropyIntegration.smallListCutoff_pos
#print axioms BinaryFormMoat.EntropyIntegration.smallListCutoff_log_gap
#print axioms BinaryFormMoat.EntropyIntegration.coverage_exception_size_lt_cutoff
#print axioms BinaryFormMoat.EntropyIntegration.overlapExceptionalCandidates_card_le_cutoff
#print axioms BinaryFormMoat.EntropyIntegration.coverage_floor_parameter_gap
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_size_failure_le_rounded_coverage
#print axioms BinaryFormMoat.EntropyIntegration.coverageTrialCount_pos
#print axioms BinaryFormMoat.EntropyIntegration.coverageTrialCount_tail
