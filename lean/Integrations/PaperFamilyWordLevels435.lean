import Integrations.DyadicRootWords435
import Integrations.PaperGeometricIndices435
import Integrations.SortedFamilyHistory435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- Every actual geometric batch scale lies below the SAME paper terminal
smoothing scale. No last-word bound is supplied by the caller. -/
theorem paperGeometricIndices_scale_le_max (d M B j : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B)
    (hj : j ∈ paperGeometricIndices d M B) :
    ((B ^ j : ℕ) : ℝ) ≤ paperScheduleMaxT d M := by
  obtain ⟨m, _, _, hhi⟩ := (mem_paperGeometricIndices d M B j hd hB).mp hj
  have hm : m.val ≤ M := by have := m.isLt; omega
  have hx := paperScheduleX_mono d hd hm
  have hp : (0 : ℝ) < (B ^ j : ℕ) := by exact_mod_cast (by positivity : 0 < B ^ j)
  unfold paperScheduleMaxT
  calc
    _ = Real.exp (Real.log (B ^ j : ℕ)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hhi.trans (mul_le_mul_of_nonneg_left hx (by norm_num)))

theorem paperFamilyWordLevel_mono (d M B : ℕ) (hB : 1 ≤ B) :
    Monotone (fun k : Fin (paperGeometricIndices d M B).card =>
      rootWordLevel d (B ^ (selectedFamilyOrder (paperGeometricIndices d M B) k).val)) := by
  intro i j hij
  apply rootWordLevel_mono d
  exact Nat.pow_le_pow_right hB ((selectedFamilyOrder (paperGeometricIndices d M B)).monotone hij)

theorem paperGeometricIndices_word_le_max (d M B j : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B)
    (hj : j ∈ paperGeometricIndices d M B) :
    ((rootWordLength d (B ^ j) : ℕ) : ℝ) ≤ paperScheduleMaxT d M := by
  have hT := paperGeometricIndices_scale_ge_two d M B j hd hB hj
  have hw : ((rootWordLength d (B ^ j) : ℕ) : ℝ) ≤ (B ^ j : ℕ) := by
    exact_mod_cast rootWordLength_le d (B ^ j) hd (by omega)
  exact hw.trans (paperGeometricIndices_scale_le_max d M B j hd hB hj)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_scale_le_max
#print axioms BinaryFormMoat.GeometryIntegration.paperFamilyWordLevel_mono
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_word_le_max
