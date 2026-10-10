import Integrations.PaperScheduleWindows435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration

/-- The exact list position of an operation, without an assumed enumeration. -/
def paperOpPosition {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0) : ℕ :=
  (paperScheduleList d M g0).idxOf a

theorem paperOpPosition_lt {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0)
    (ha : a ∈ paperScheduledOps d M g0) :
    paperOpPosition a < (paperScheduleList d M g0).length :=
  List.idxOf_lt_length_of_mem ((paperScheduleList_mem a).mpr ha)

theorem paperOpPosition_get {d M : ℕ} {g0 : ℝ} (a : PaperScheduleOp d M g0)
    (ha : a ∈ paperScheduledOps d M g0) :
    (paperScheduleList d M g0).get ⟨paperOpPosition a, paperOpPosition_lt a ha⟩ = a := by
  exact List.getElem_idxOf (paperOpPosition_lt a ha)

/-- The certified sort order is equivalent to the numerical index order. -/
theorem paperScheduleList_get_later_iff {d M : ℕ} {g0 : ℝ}
    (i j : Fin (paperScheduleList d M g0).length) :
    paperOpLater ((paperScheduleList d M g0).get i) ((paperScheduleList d M g0).get j) ↔ i ≤ j := by
  constructor
  · intro h
    by_contra hn
    have hj : j ≤ i := by omega
    have he := paperOpLater_antisymm _ _ h (paperScheduleList_get_later d M g0 j i hj)
    have hi := (paperScheduleList_nodup d M g0).injective_get he
    omega
  · exact paperScheduleList_get_later d M g0 i j

theorem paperOpPosition_le_iff {d M : ℕ} {g0 : ℝ} (a b : PaperScheduleOp d M g0)
    (ha : a ∈ paperScheduledOps d M g0) (hb : b ∈ paperScheduledOps d M g0) :
    paperOpPosition a ≤ paperOpPosition b ↔ paperOpLater a b := by
  have h := paperScheduleList_get_later_iff
    ⟨paperOpPosition a, paperOpPosition_lt a ha⟩ ⟨paperOpPosition b, paperOpPosition_lt b hb⟩
  rw [paperOpPosition_get a ha, paperOpPosition_get b hb] at h
  exact h.symm

/-- No other window or band can occur between successive ordinals. -/
theorem paperOp_between_successive {d M : ℕ} {g0 : ℝ} (m : Fin (M + 1)) (b : Fin 3)
    (n : ℕ) (hn : n + 1 < paperBandOperationCount d M m.val g0 b)
    (c : PaperScheduleOp d M g0)
    (hleft : paperOpLater ⟨m, b, ⟨n, by omega⟩⟩ c)
    (hright : paperOpLater c ⟨m, b, ⟨n + 1, hn⟩⟩) :
    c = ⟨m, b, ⟨n, by omega⟩⟩ ∨ c = ⟨m, b, ⟨n + 1, hn⟩⟩ := by
  rcases c with ⟨mc, bc, nc⟩
  unfold paperOpLater at hleft hright
  dsimp at hleft hright
  have hm : mc = m := Fin.ext (by omega)
  subst mc
  have hb : bc = b := Fin.ext (by omega)
  subst bc
  have he : nc.val = n ∨ nc.val = n + 1 := by omega
  rcases he with he | he
  · left; congr 2; exact Fin.ext he
  · right; congr 2; exact Fin.ext he

theorem paperOpPosition_successive {d M : ℕ} {g0 : ℝ} (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (b : Fin 3) (n : ℕ)
    (hn : n + 1 < paperBandOperationCount d M m.val g0 b) :
    paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n + 1, hn⟩⟩ =
      paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, by omega⟩⟩ + 1 := by
  let a : PaperScheduleOp d M g0 := ⟨m, b, ⟨n, by omega⟩⟩
  let a' : PaperScheduleOp d M g0 := ⟨m, b, ⟨n + 1, hn⟩⟩
  have mem (t : Fin (paperBandOperationCount d M m.val g0 b)) :
      (⟨m, b, t⟩ : PaperScheduleOp d M g0) ∈ paperScheduledOps d M g0 := by
    simpa only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have ha := mem a.2.2
  have ha' := mem a'.2.2
  have hlt : paperOpPosition a < paperOpPosition a' := by
    have hle := (paperOpPosition_le_iff a a' ha ha').mpr (by unfold paperOpLater; dsimp [a, a']; omega)
    have hne : paperOpPosition a ≠ paperOpPosition a' := by
      intro he
      have he' : (⟨paperOpPosition a, paperOpPosition_lt a ha⟩ : Fin (paperScheduleList d M g0).length) =
          ⟨paperOpPosition a', paperOpPosition_lt a' ha'⟩ := Fin.ext he
      have hv := congrArg (fun i => ((paperScheduleList d M g0).get i).2.2.val) he'
      rw [paperOpPosition_get a ha, paperOpPosition_get a' ha'] at hv
      dsimp [a, a'] at hv
      omega
    omega
  let i : Fin (paperScheduleList d M g0).length := ⟨paperOpPosition a + 1, by
    have h := paperOpPosition_lt a' ha'; omega⟩
  have hl := paperScheduleList_get_later d M g0 ⟨paperOpPosition a, paperOpPosition_lt a ha⟩ i
    (by simp only [Fin.le_iff_val_le_val]; dsimp [i]; omega)
  have hr := paperScheduleList_get_later d M g0 i ⟨paperOpPosition a', paperOpPosition_lt a' ha'⟩
    (by simp only [Fin.le_iff_val_le_val]; dsimp [i]; omega)
  rw [paperOpPosition_get a ha] at hl
  rw [paperOpPosition_get a' ha'] at hr
  rcases paperOp_between_successive m b n hn _ hl hr with he | he
  · have hj := (paperScheduleList_nodup d M g0).injective_get
      (he.trans (paperOpPosition_get a ha).symm)
    have hv := congrArg Fin.val hj
    dsimp [i] at hv
    omega
  · have hj := (paperScheduleList_nodup d M g0).injective_get
      (he.trans (paperOpPosition_get a' ha').symm)
    have hv := congrArg Fin.val hj
    dsimp [i] at hv
    exact hv.symm

/-- Every ordinal block is an ACTUAL contiguous interval of the full schedule. -/
theorem paperOpPosition_block {d M : ℕ} {g0 : ℝ} (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (b : Fin 3) (n j : ℕ)
    (hfit : n + j < paperBandOperationCount d M m.val g0 b) :
    paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n + j, hfit⟩⟩ =
      paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, by omega⟩⟩ + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := paperOpPosition_successive (d := d) (g0 := g0) m hm b (n + j)
      (by omega)
    have hi := ih (by omega)
    simpa only [Nat.add_assoc] using hs.trans (congrArg (fun t => t + 1) hi)

theorem paperScheduleWindow_block {d M : ℕ} {g0 : ℝ} (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (b : Fin 3) (n j : ℕ)
    (hfit : n + j < paperBandOperationCount d M m.val g0 b) :
    paperScheduleWindow d M g0
      (paperOpPosition (d := d) (g0 := g0) ⟨m, b, ⟨n, by omega⟩⟩ + j) =
      paperWalkWindow (paperBandScale (Real.exp (paperBandHi d m.val b)) (paperBandG M g0 b) (n + j))
        (paperBandG M g0 b) := by
  let o : PaperScheduleOp d M g0 := ⟨m, b, ⟨n + j, hfit⟩⟩
  have ho : o ∈ paperScheduledOps d M g0 := by
    simpa only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  rw [← paperOpPosition_block m hm b n j hfit]
  have h := paperScheduleWindow_get d M g0 ⟨paperOpPosition o, paperOpPosition_lt o ho⟩
  rw [paperOpPosition_get o ho] at h
  exact h

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_lt
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_get
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleList_get_later_iff
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_le_iff
#print axioms BinaryFormMoat.GeometryIntegration.paperOp_between_successive
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_successive
#print axioms BinaryFormMoat.GeometryIntegration.paperOpPosition_block
#print axioms BinaryFormMoat.GeometryIntegration.paperScheduleWindow_block
