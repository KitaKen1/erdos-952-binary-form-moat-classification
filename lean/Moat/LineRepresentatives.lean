import Moat.BoxLineWitness
import Moat.DeterminantGeometry
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination

namespace BinaryFormMoat

/-- The finite integer rectangle; neither coordinate needs to be nonzero. -/
def rectanglePoints (A B : ℕ) : Finset Point :=
  Finset.Icc (-(A : ℤ)) A ×ˢ Finset.Icc (-(B : ℤ)) B

theorem mem_rectanglePoints (z : Point) (A B : ℕ) :
    z ∈ rectanglePoints A B ↔ z.1.natAbs ≤ A ∧ z.2.natAbs ≤ B := by
  simp only [rectanglePoints, Finset.mem_product, Finset.mem_Icc]
  omega

/-- Dividing both coordinates by their gcd gives a primitive vector without
increasing either coordinate bound. -/
theorem exists_primitive_multiple (z : Point) (hz : z ≠ (0, 0)) :
    ∃ v : Point, IsCoprime v.1 v.2 ∧ ∃ a : ℤ, a ≠ 0 ∧
      z = (a * v.1, a * v.2) ∧ v.1.natAbs ≤ z.1.natAbs ∧
        v.2.natAbs ≤ z.2.natAbs := by
  have hcoord : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (Prod.ext h.1 h.2)
  have hg : 0 < Int.gcd z.1 z.2 := Int.gcd_pos_iff.mpr hcoord
  obtain ⟨x, y, hprim, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨(x, y), Int.isCoprime_iff_gcd_eq_one.mpr hprim,
    (Int.gcd z.1 z.2 : ℤ), by exact_mod_cast hg.ne', ?_, ?_, ?_⟩
  · exact Prod.ext (by simpa [mul_comm] using hx) (by simpa [mul_comm] using hy)
  · rw [hx, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ hg
  · rw [hy, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ hg

/-- A primitive integer vector generates every integer point on its rational
line. Bezout gives the multiplier directly, including vertical lines. -/
theorem exists_int_multiple_of_determinant_zero (z w : Point)
    (hz : IsCoprime z.1 z.2) (hdet : determinant z w = 0) :
    ∃ a : ℤ, w = (a * z.1, a * z.2) := by
  obtain ⟨u, v, huv⟩ := hz
  refine ⟨u * w.1 + v * w.2, Prod.ext ?_ ?_⟩
  · dsimp
    dsimp [determinant] at hdet
    linear_combination -w.1 * huv - v * hdet
  · dsimp
    dsimp [determinant] at hdet
    linear_combination -w.2 * huv + u * hdet

/-- A greedy finite selection removes duplicate rational lines. Only symmetry
and reflexivity of determinant-zero are needed for this covering statement. -/
theorem exists_noncollinear_cover (s : Finset Point) :
    ∃ t : Finset Point, t ⊆ s ∧
      (∀ z ∈ t, ∀ w ∈ t, z ≠ w → determinant z w ≠ 0) ∧
      ∀ z ∈ s, ∃ w ∈ t, determinant w z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨t, hsub, hsep, hcover⟩ := ih
    by_cases h : ∃ w ∈ t, determinant w x = 0
    · refine ⟨t, fun z hz => Finset.mem_insert_of_mem (hsub hz), hsep, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hzEq | hzOld
      · subst z; exact h
      · exact hcover z hzOld
    · refine ⟨insert x t, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · intro z hz w hw hne
        rcases Finset.mem_insert.mp hz with hzEq | hzOld
        · subst z
          rcases Finset.mem_insert.mp hw with hwEq | hwOld
          · subst w; exact (hne rfl).elim
          · intro hdet
            apply h
            refine ⟨w, hwOld, ?_⟩
            dsimp [determinant] at hdet ⊢
            linear_combination -hdet
        · rcases Finset.mem_insert.mp hw with hwEq | hwOld
          · subst w; exact fun hdet => h ⟨z, hzOld, hdet⟩
          · exact hsep z hzOld w hwOld hne
      · intro z hz
        rcases Finset.mem_insert.mp hz with hzEq | hzOld
        · subst z; exact ⟨x, Finset.mem_insert_self _ _, by dsimp [determinant]; ring⟩
        · obtain ⟨w, hw, hdet⟩ := hcover z hzOld
          exact ⟨w, Finset.mem_insert_of_mem hw, hdet⟩

/-- Every nonzero point in the rectangle belongs to exactly one selected
rational line. Representatives are primitive and remain in the rectangle. -/
theorem exists_rectangle_line_representatives (A B : ℕ) :
    ∃ s : Finset Point,
      (∀ z ∈ s, IsCoprime z.1 z.2 ∧ z ∈ rectanglePoints A B) ∧
      (∀ z ∈ s, ∀ w ∈ s, z ≠ w → determinant z w ≠ 0) ∧
      ∀ z ∈ rectanglePoints A B, z ≠ (0, 0) →
        ∃ w ∈ s, ∃ a : ℤ, a ≠ 0 ∧ z = (a * w.1, a * w.2) := by
  classical
  let candidates := (rectanglePoints A B).filter fun z => IsCoprime z.1 z.2
  obtain ⟨s, hsub, hsep, hcover⟩ := exists_noncollinear_cover candidates
  refine ⟨s, ?_, hsep, ?_⟩
  · intro z hz
    obtain ⟨hrect, hprim⟩ := Finset.mem_filter.mp (hsub hz)
    exact ⟨hprim, hrect⟩
  · intro z hz hne
    obtain ⟨v, hv, a, ha, he, hx, hy⟩ := exists_primitive_multiple z hne
    have hrect := (mem_rectanglePoints z A B).mp hz
    have hvc : v ∈ candidates := Finset.mem_filter.mpr
      ⟨(mem_rectanglePoints v A B).mpr ⟨hx.trans hrect.1, hy.trans hrect.2⟩, hv⟩
    obtain ⟨w, hw, hdet⟩ := hcover v hvc
    have hwprim := (Finset.mem_filter.mp (hsub hw)).2
    obtain ⟨c, hc⟩ := exists_int_multiple_of_determinant_zero w v hwprim hdet
    have hmul : z = ((a * c) * w.1, (a * c) * w.2) := by
      rw [he, hc]
      simp only [mul_assoc]
    refine ⟨w, hw, a * c, ?_, hmul⟩
    intro hzero
    apply hne
    simpa [hzero] using hmul

end BinaryFormMoat
