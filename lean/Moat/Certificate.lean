import Moat.Basic
import Mathlib.Tactic.Abel

namespace BinaryFormMoat

/-- An edge invariant and a finite label bound each component if the pair recovers vertices.
The invariant need not itself have finite range. -/
theorem component_bound_of_label {V α κ : Type*} [Fintype α] (G : SimpleGraph V)
    (label : V → α) (cell : V → κ)
    (hedge : ∀ ⦃x y⦄, G.Adj x y → cell x = cell y)
    (hrecover : ∀ x y, cell x = cell y → label x = label y → x = y) (z : V) :
    Set.encard {w | G.Reachable z w} ≤ (Fintype.card α : ℕ∞) := by
  have invariant {x y} (h : G.Reachable x y) : cell x = cell y := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => rfl
    | cons hadj _ ih => exact (hedge hadj).trans ih
  have hinj : Set.InjOn label {w | G.Reachable z w} := by
    intro x hx y hy hxy
    exact hrecover x y ((invariant hx).symm.trans (invariant hy)) hxy
  have hcard := Set.encard_le_encard_of_injOn
    (t := (Set.univ : Set α)) (fun _ _ => Set.mem_univ _) hinj
  simpa using hcard

/-- A finite labelling and a displacement potential certify a component-size bound.
The hypothesis is local to edges, so a periodic finite quotient can supply it.
This avoids passing through infinite walks and König's lemma. -/
theorem component_bound_of_potential (F : Form) (r R : ℕ)
    {α : Type*} [Fintype α]
    (label : {z : Point // Allowed F r z} → α) (lift : α → Point)
    (hedge : ∀ ⦃z w⦄, (graph F r R).Adj z w →
      z.val - lift (label z) = w.val - lift (label w))
    (z : {z : Point // Allowed F r z}) :
    Set.encard {w | (graph F r R).Reachable z w} ≤ (Fintype.card α : ℕ∞) := by
  have invariant {x y} (h : (graph F r R).Reachable x y) :
      x.val - lift (label x) = y.val - lift (label y) := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => rfl
    | cons hadj _ ih => exact (hedge hadj).trans ih
  have hinj : Set.InjOn label {w | (graph F r R).Reachable z w} := by
    intro x hx y hy hxy
    have hi := (invariant hx).symm.trans (invariant hy)
    rw [hxy] at hi
    exact Subtype.ext (sub_left_inj.mp hi)
  have hcard := Set.encard_le_encard_of_injOn
    (t := (Set.univ : Set α)) (fun _ _ => Set.mem_univ _) hinj
  simpa using hcard

end BinaryFormMoat
