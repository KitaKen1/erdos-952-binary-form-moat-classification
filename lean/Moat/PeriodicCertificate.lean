import Moat.LinearFactors

namespace BinaryFormMoat

abbrev Residue (Q : ℕ) := ZMod Q × ZMod Q

def residue (Q : ℕ) (z : Point) : Residue Q := ((z.1 : ZMod Q), (z.2 : ZMod Q))

/-- A finite enumeration of all potentially relevant displacements. -/
def finiteStep (S : ℕ) (i : Fin (2 * S + 1) × Fin (2 * S + 1)) : Point :=
  ((i.1.val : ℤ) - S, (i.2.val : ℤ) - S)

/-- Every bounded step is in the finite displacement table. -/
theorem exists_finiteStep (R : ℕ) (z w : Point) (h : sqDist z w ≤ (R : ℤ)) :
    ∃ i : Fin (2 * (R + 1) + 1) × Fin (2 * (R + 1) + 1),
      finiteStep (R + 1) i = w - z := by
  have hx := linear_step_bound 1 0 R z w h
  have hy := linear_step_bound 0 1 R z w h
  simp only [Int.natAbs_one, Int.natAbs_zero, zero_add, one_mul,
    zero_mul, add_zero] at hx hy
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  let i : Fin (2 * (R + 1) + 1) := ⟨(w.1 - z.1 + (R + 1 : ℕ)).toNat, by omega⟩
  let j : Fin (2 * (R + 1) + 1) := ⟨(w.2 - z.2 + (R + 1 : ℕ)).toNat, by omega⟩
  refine ⟨(i, j), Prod.ext ?_ ?_⟩ <;> dsimp [finiteStep, i, j] <;> omega

/-- A finite local certificate for a periodic superset of the allowed vertices.
The relation is decidable for concrete `Q`, `R`, `good`, and `lift`. -/
def PeriodicPotentialCheck (Q R : ℕ) (good : Residue Q → Prop)
    (lift : Residue Q → Point) : Prop :=
  ∀ u : Residue Q, ∀ i : Fin (2 * (R + 1) + 1) × Fin (2 * (R + 1) + 1),
    good u → sqDist (0, 0) (finiteStep (R + 1) i) ≤ (R : ℤ) →
    good (u + residue Q (finiteStep (R + 1) i)) →
    lift (u + residue Q (finiteStep (R + 1) i)) = lift u + finiteStep (R + 1) i

/-- Kernel-checking finite local equations certifies every infinite-lattice component. -/
theorem component_bound_of_periodic_check (F : Form) (r R Q : ℕ) [NeZero Q]
    (good : Residue Q → Prop) (lift : Residue Q → Point)
    (hsub : ∀ z, Allowed F r z → good (residue Q z))
    (hcheck : PeriodicPotentialCheck Q R good lift)
    (z : {z : Point // Allowed F r z}) :
    Set.encard {w | (graph F r R).Reachable z w} ≤ (Q * Q : ℕ) := by
  have hbound := component_bound_of_potential F r R
    (fun z => residue Q z.val) lift (z := z)
  simp only [Fintype.card_prod, ZMod.card] at hbound
  apply hbound
  intro x y hxy
  obtain ⟨i, hi⟩ := exists_finiteStep R x.val y.val hxy.2
  have hr : residue Q y.val = residue Q x.val + residue Q (finiteStep (R + 1) i) := by
    rw [hi]
    apply Prod.ext <;> simp [residue]
  have hs : sqDist (0, 0) (finiteStep (R + 1) i) ≤ (R : ℤ) := by
    rw [hi]
    have he : sqDist (0, 0) (y.val - x.val) = sqDist x.val y.val := by
      dsimp [sqDist]
      ring
    exact he ▸ hxy.2
  have he := hcheck (residue Q x.val) i (hsub x.val x.property) hs
    (by rw [← hr]; exact hsub y.val y.property)
  rw [← hr, hi] at he
  rw [he]
  abel

end BinaryFormMoat
