import Integrations.PassingLists435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Reverse-engineer the survivor quota; keep at least one package. -/
noncomputable def passingPackageCount (C : ℕ) (ε M : ℝ) : ℕ :=
  max 1 ⌈Real.log ((C : ℝ) / M) / ε⌉₊

theorem passingPackageCount_pos (C : ℕ) (ε M : ℝ) :
    0 < passingPackageCount C ε M :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem passingPackageCount_exponent (C : ℕ) (ε M : ℝ) (hε : 0 < ε) :
    Real.log ((C : ℝ) / M) ≤ (passingPackageCount C ε M : ℝ) * ε := by
  have hc : Real.log ((C : ℝ) / M) / ε ≤ (passingPackageCount C ε M : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right 1 _))
  exact (div_le_iff₀ hε).mp hc

theorem passingPackageCount_tail (C : ℕ) (hC : 0 < C) (ε M : ℝ)
    (hε : 0 < ε) (hM : 0 < M) :
    (C : ℝ) * Real.exp (-(passingPackageCount C ε M : ℝ) * ε) ≤ M := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hc := passingPackageCount_exponent C ε M hε
  have he : Real.exp (-(passingPackageCount C ε M : ℝ) * ε) ≤
      Real.exp (-Real.log ((C : ℝ) / M)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h := mul_le_mul_of_nonneg_left he hC'.le
  rw [Real.exp_neg, Real.exp_log (div_pos hC' hM)] at h
  convert h using 1
  field_simp

/-- The explicit integer choice costs less than one extra package. -/
theorem passingPackageCount_le (C : ℕ) (ε M : ℝ) (hε : 0 < ε)
    (hM : 0 < M) (hMC : M ≤ (C : ℝ)) :
    (passingPackageCount C ε M : ℝ) ≤ 1 + Real.log ((C : ℝ) / M) / ε := by
  have hlog : 0 ≤ Real.log ((C : ℝ) / M) :=
    Real.log_nonneg ((one_le_div hM).mpr hMC)
  have hq : 0 ≤ Real.log ((C : ℝ) / M) / ε := div_nonneg hlog hε.le
  have hc := Nat.ceil_lt_add_one hq
  unfold passingPackageCount
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · linarith

/-- A per-coordinate package count is constructed from the hit floor.
Selecting one common count and paying its shared-data cost is a later step. -/
theorem expected_passingList_card_constructed_quota
    {C H : Type*} [Fintype C] [Nonempty C] [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (ν : Measure H) [IsProbabilityMeasure ν] (reject : C → H → Prop)
    (B : Finset C) (ε M : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hfloor : ∀ x ∉ B, ε ≤ ν.real {h | reject x h}) (hB : (B.card : ℝ) ≤ 4 * M) :
    (∫ h : Fin (passingPackageCount (Fintype.card C) ε M) → H,
      ((passingList reject h).card : ℝ)
      ∂Measure.pi (fun _ : Fin (passingPackageCount (Fintype.card C) ε M) => ν)) ≤ 5 * M := by
  apply expected_passingList_card_source_bound ν reject B ε M hfloor hB
  simpa only [Fintype.card_fin] using
    passingPackageCount_tail (Fintype.card C) Fintype.card_pos ε M hε hM

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.passingPackageCount_pos
#print axioms BinaryFormMoat.EntropyIntegration.passingPackageCount_exponent
#print axioms BinaryFormMoat.EntropyIntegration.passingPackageCount_tail
#print axioms BinaryFormMoat.EntropyIntegration.passingPackageCount_le
#print axioms BinaryFormMoat.EntropyIntegration.expected_passingList_card_constructed_quota
