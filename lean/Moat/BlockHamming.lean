import Moat.BalancedEncoding
import Mathlib.InformationTheory.Hamming

namespace BinaryFormMoat

/-- Changing a block requires changing at least one entry of that block.
This needs no special numerical interpretation of a binary word. -/
theorem block_hamming_le_flat {ι κ C : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [DecidableEq C] (x y : ι → κ → C) :
    hammingDist x y ≤ hammingDist (fun q : ι × κ => x q.1 q.2)
      (fun q : ι × κ => y q.1 q.2) := by
  classical
  have hex : ∀ i, x i ≠ y i → ∃ j, x i j ≠ y i j := by
    intro i hi
    by_contra hn
    exact hi (funext fun j => by simpa using not_exists.mp hn j)
  let f : {i // i ∈ (Finset.univ.filter fun i => x i ≠ y i)} →
      {q // q ∈ (Finset.univ.filter fun q : ι × κ => x q.1 q.2 ≠ y q.1 q.2)} :=
    fun i => ⟨(i.val, Classical.choose (hex i.val (Finset.mem_filter.mp i.property).2)),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Classical.choose_spec (hex i.val (Finset.mem_filter.mp i.property).2)⟩⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro i j hij
  exact Subtype.ext (congrArg (fun q => q.val.1) hij)

/-- An injective block code cannot hide a change in the root label. -/
theorem root_hamming_le_encoded {ι A : Type*} [Fintype ι]
    {K B : ι → Type*} [∀ i, DecidableEq (K i)] [∀ i, DecidableEq (B i)]
    (e : ∀ i, K i × A ↪ B i) (x y : (∀ i, K i) × (ι → A)) :
    hammingDist x.1 y.1 ≤ hammingDist (blockEncoding e x) (blockEncoding e y) := by
  classical
  apply Finset.card_le_card
  intro i hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro he
  exact (Finset.mem_filter.mp hi).2 (congrArg Prod.fst ((e i).injective he))

/-- The full bridge to the ambient b*k-dimensional binary cube. Auxiliary
labels do not count as extra root changes. -/
theorem root_hamming_le_bits {ι A : Type*} [Fintype ι]
    {K : ι → Type*} [∀ i, DecidableEq (K i)] (b : ℕ)
    (e : ∀ i, K i × A ↪ (Fin b → Bool))
    (x y : (∀ i, K i) × (ι → A)) :
    hammingDist x.1 y.1 ≤
      hammingDist (fun q : ι × Fin b => blockEncoding e x q.1 q.2)
        (fun q : ι × Fin b => blockEncoding e y q.1 q.2) :=
  (root_hamming_le_encoded e x y).trans
    (block_hamming_le_flat (blockEncoding e x) (blockEncoding e y))

/-- Taking Hamming neighborhoods of radius r preserves disjointness of
classes whose points are separated by more than 2*r. -/
theorem hamming_neighborhoods_disjoint {ι : Type*} [Fintype ι]
    {K : ι → Type*} [∀ i, DecidableEq (K i)]
    (A B : Set (∀ i, K i)) (r : ℕ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, 2 * r < hammingDist x y) :
    Disjoint {z | ∃ x ∈ A, hammingDist x z ≤ r}
      {z | ∃ y ∈ B, hammingDist y z ≤ r} := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have ht := hammingDist_triangle_right x y z
  have hs := hsep x hx y hy
  omega

end BinaryFormMoat
