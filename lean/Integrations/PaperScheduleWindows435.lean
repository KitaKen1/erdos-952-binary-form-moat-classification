import Integrations.PaperFutureShift435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- The actual sorted schedule's windows, extended by zero after its end. -/
def paperScheduleWindow (d M : ℕ) (g0 : ℝ) (n : ℕ) : ℕ :=
  if h : n < (paperScheduleList d M g0).length then
    let a := (paperScheduleList d M g0).get ⟨n, h⟩
    paperWalkWindow (paperOpU a) (paperOpG a)
  else 0

theorem paperScheduleWindow_get (d M : ℕ) (g0 : ℝ)
    (n : Fin (paperScheduleList d M g0).length) :
    paperScheduleWindow d M g0 n.val =
      paperWalkWindow (paperOpU ((paperScheduleList d M g0).get n))
        (paperOpG ((paperScheduleList d M g0).get n)) := by
  simp [paperScheduleWindow, n.isLt]

theorem paperScheduleWindow_after (d M n : ℕ) (g0 : ℝ)
    (hn : (paperScheduleList d M g0).length ≤ n) :
    paperScheduleWindow d M g0 n = 0 := by simp [paperScheduleWindow, Nat.not_lt.mpr hn]

theorem paperScheduleList_nodup (d M : ℕ) (g0 : ℝ) :
    (paperScheduleList d M g0).Nodup := Finset.sort_nodup _ _

theorem paperScheduleList_get_mem (d M : ℕ) (g0 : ℝ)
    (n : Fin (paperScheduleList d M g0).length) :
    (paperScheduleList d M g0).get n ∈ paperScheduledOps d M g0 :=
  (paperScheduleList_mem _).mp (List.get_mem _ _)

theorem paperScheduleList_get_later (d M : ℕ) (g0 : ℝ)
    (i j : Fin (paperScheduleList d M g0).length) (hij : i ≤ j) :
    paperOpLater ((paperScheduleList d M g0).get i) ((paperScheduleList d M g0).get j) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hij
  · exact paperOpLater_refl _
  · exact (paperScheduleList_pairwise d M g0).rel_get_of_lt hlt

/-- Injecting remaining list indices into the actual future operation set pays
for each window once, without a cardinality or maximum-window approximation. -/
theorem paperScheduleWindow_suffix_sum_le (d M : ℕ) (g0 : ℝ)
    (k : Fin (paperScheduleList d M g0).length) (n : ℕ)
    (hn : n ≤ (paperScheduleList d M g0).length - k.val) :
    (∑ j ∈ Finset.range n, paperScheduleWindow d M g0 (k.val + j)) ≤
      ∑ a ∈ (paperScheduledOps d M g0).filter
        (paperOpLater ((paperScheduleList d M g0).get k)), paperWalkWindow (paperOpU a) (paperOpG a) := by
  let f (j : Fin n) : PaperScheduleOp d M g0 :=
    (paperScheduleList d M g0).get ⟨k.val + j.val, by omega⟩
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum_of_injOn f
  · intro i _ j _ hij
    have he := (paperScheduleList_nodup d M g0).injective_get hij
    have hv := congrArg Fin.val he
    exact Fin.ext (by dsimp at hv; omega)
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_filter.mpr
    exact ⟨paperScheduleList_get_mem d M g0 _,
      paperScheduleList_get_later d M g0 k _ (by simp only [Fin.le_iff_val_le_val]; omega)⟩
  · intro j _
    exact (paperScheduleWindow_get d M g0 ⟨k.val + j.val, by omega⟩).le
  · intro a _ _
    exact Nat.zero_le _

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleWindow
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleWindow_get
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleWindow_after
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_nodup
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_get_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_get_later
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleWindow_suffix_sum_le
