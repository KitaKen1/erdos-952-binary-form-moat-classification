import Integrations.LogGridWindow435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

def paperLogGridWindow (d B m : ℕ) : Finset ℕ :=
  logGridWindow (paperScheduleX d m) (Real.log B)

/-- Distinct logarithmic windows are strictly separated. This prevents
double counting in the lower budget; sparse gaps cost nothing. -/
theorem paper_log_window_gap (d m n : ℕ) (hd : 1 ≤ d) (hmn : m < n) :
    (21 / 20 : ℝ) * paperScheduleX d m < paperScheduleX d n := by
  have hx := paperScheduleX_pos d m hd
  have hb : (100 : ℝ) ≤ paperScheduleBase d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold paperScheduleBase
    linarith
  have hnext := paperScheduleX_mono d hd (by omega : m + 1 ≤ n)
  rw [paperScheduleX_succ] at hnext
  exact (mul_lt_mul_of_pos_right (by linarith : (21 / 20 : ℝ) < paperScheduleBase d) hx).trans_le hnext

theorem paperLogGridWindow_pairwise (d B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    Pairwise (fun m n => Disjoint (paperLogGridWindow d B m) (paperLogGridWindow d B n)) := by
  intro m n hmn
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  apply Finset.disjoint_left.mpr
  intro j hjm hjn
  have hm := (mem_logGridWindow _ _ (paperScheduleX_pos d m hd).le hh j).mp hjm
  have hn := (mem_logGridWindow _ _ (paperScheduleX_pos d n hd).le hh j).mp hjn
  rcases lt_or_gt_of_ne hmn with h | h
  · have := paper_log_window_gap d m n hd h
    linarith
  · have := paper_log_window_gap d n m hd h
    linarith

/-- The actual finite index set is EXACTLY the union of its upper-half
window grids, rather than an arbitrary subset with an assumed large sum. -/
theorem paperGeometricIndices_eq_biUnion (d M B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    paperGeometricIndices d M B =
      (Finset.Icc ((M + 1) / 2) M).biUnion (paperLogGridWindow d B) := by
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  ext j
  rw [mem_paperGeometricIndices d M B j hd hB, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, hlo, hhi⟩
    refine ⟨m.val, Finset.mem_Icc.mpr ⟨hm, by omega⟩, ?_⟩
    rw [Nat.cast_pow, Real.log_pow] at hlo hhi
    exact (mem_logGridWindow _ _ (paperScheduleX_pos d m.val hd).le hh j).mpr ⟨hlo, hhi⟩
  · rintro ⟨m, hm, hj⟩
    obtain ⟨hlo, hhi⟩ := (mem_logGridWindow _ _ (paperScheduleX_pos d m hd).le hh j).mp hj
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    refine ⟨⟨m, by omega⟩, hmlo, ?_, ?_⟩ <;>
      simpa only [Nat.cast_pow, Real.log_pow] using ‹_›

theorem paperGeometricLogBudget_eq_sum_windows (d M B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    paperGeometricLogBudget d M B =
      ∑ m ∈ Finset.Icc ((M + 1) / 2) M,
        ∑ j ∈ paperLogGridWindow d B m, 1 / ((j : ℝ) * Real.log B) := by
  unfold paperGeometricLogBudget
  rw [paperGeometricIndices_eq_biUnion d M B hd hB,
    Finset.sum_biUnion (fun m _ n _ hmn => paperLogGridWindow_pairwise d B hd hB hmn)]
  simp only [Nat.cast_pow, Real.log_pow]

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperLogGridWindow
#print axioms BinaryFormMoat.GeometryIntegration.paper_log_window_gap
#print axioms BinaryFormMoat.GeometryIntegration.paperLogGridWindow_pairwise
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_eq_biUnion
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricLogBudget_eq_sum_windows
