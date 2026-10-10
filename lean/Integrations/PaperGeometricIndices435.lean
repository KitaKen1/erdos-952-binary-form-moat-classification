import Integrations.GeometricBatches435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- ALL used integer powers in the paper's upper-half windows, truncated by
a derived finite upper bound. The truncation is proved lossless below. -/
def paperGeometricIndices (d M B : ℕ) : Finset ℕ :=
  (Finset.range (⌈((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B⌉₊ + 1)).filter
    (fun j => ∃ m : Fin (M + 1), (M + 1) / 2 ≤ m.val ∧
      paperScheduleX d m.val ≤ Real.log (B ^ j : ℕ) ∧
      Real.log (B ^ j : ℕ) ≤ (21 / 20 : ℝ) * paperScheduleX d m.val)

theorem mem_paperGeometricIndices (d M B j : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    j ∈ paperGeometricIndices d M B ↔
      ∃ m : Fin (M + 1), (M + 1) / 2 ≤ m.val ∧
        paperScheduleX d m.val ≤ Real.log (B ^ j : ℕ) ∧
        Real.log (B ^ j : ℕ) ≤ (21 / 20 : ℝ) * paperScheduleX d m.val := by
  rw [paperGeometricIndices, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨m, _, _, hhi⟩ := h
    have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
    have hx := paperScheduleX_mono d hd (by omega : m.val ≤ M)
    have hb : (j : ℝ) ≤ ((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B := by
      apply (le_div_iff₀ hlog).mpr
      rw [Nat.cast_pow, Real.log_pow] at hhi
      nlinarith
    have hj : j ≤ ⌈((21 / 20 : ℝ) * paperScheduleX d M) / Real.log B⌉₊ := by
      exact_mod_cast hb.trans (Nat.le_ceil _)
    exact Finset.mem_range.mpr (by omega)

theorem paperGeometricIndices_scale_ge_two (d M B j : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B)
    (hj : j ∈ paperGeometricIndices d M B) : 2 ≤ B ^ j := by
  obtain ⟨m, _, hlo, _⟩ := (mem_paperGeometricIndices d M B j hd hB).mp hj
  have hx := paperScheduleX_pos d m.val hd
  have hjpos : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    simp only [this, pow_zero, Nat.cast_one, Real.log_one] at hlo
    linarith
  have hp := Nat.pow_le_pow_right (by omega : 0 < B) hjpos
  rw [pow_one] at hp
  exact (show 2 ≤ B by omega).trans hp

/-- The used progression's logarithmic reciprocal budget is a finite sum;
its divergence as M grows remains a separate analytic obligation. -/
def paperGeometricLogBudget (d M B : ℕ) : ℝ :=
  ∑ j ∈ paperGeometricIndices d M B, 1 / Real.log (B ^ j : ℕ)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices
#print axioms BinaryFormMoat.GeometryIntegration.mem_paperGeometricIndices
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_scale_ge_two
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricLogBudget
