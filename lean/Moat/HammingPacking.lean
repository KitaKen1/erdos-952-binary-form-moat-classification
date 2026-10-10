import Moat.BlockHamming
import Moat.HammingGeometry

namespace BinaryFormMoat

section Packing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

theorem hammingNeighborhood_disjoint (r : ℕ) (A B : Finset (∀ i, K i))
    (hsep : ∀ x ∈ A, ∀ y ∈ B, 2 * r < hammingDist x y) :
    Disjoint (hammingNeighborhood r A) (hammingNeighborhood r B) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, hxz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨y, hy, hyz⟩ := (Finset.mem_filter.mp hz').2
  have ht := hammingDist_triangle_right x y z
  have hs := hsep x hx y hy
  omega

/-- Expansion and arithmetic separation combine without a union-bound factor
equal to the number of lines. The expansion input is explicit and is not
asserted by this theorem. -/
theorem separated_expansion_packing {J : Type*} [DecidableEq J]
    (s : Finset J) (A : J → Finset (∀ i, K i)) (r : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ A i, ∀ y ∈ A j, 2 * r < hammingDist x y)
    (hexpand : ∀ i ∈ s, L * ((A i).card : ℝ) ≤ (hammingNeighborhood r (A i)).card) :
    L * ((s.biUnion A).card : ℝ) ≤ Fintype.card (∀ i, K i) := by
  have hdis : (s : Set J).PairwiseDisjoint (fun i => hammingNeighborhood r (A i)) := by
    intro i hi j hj hij
    exact hammingNeighborhood_disjoint r (A i) (A j) (hsep i hi j hj hij)
  calc
    _ ≤ L * ∑ i ∈ s, ((A i).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact_mod_cast (Finset.card_biUnion_le : (s.biUnion A).card ≤ ∑ i ∈ s, (A i).card)
    _ = ∑ i ∈ s, L * ((A i).card : ℝ) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, ((hammingNeighborhood r (A i)).card : ℝ) :=
      Finset.sum_le_sum hexpand
    _ = ((s.biUnion fun i => hammingNeighborhood r (A i)).card : ℝ) := by
      rw [Finset.card_biUnion hdis, Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast Finset.card_le_univ _

end Packing

end BinaryFormMoat
