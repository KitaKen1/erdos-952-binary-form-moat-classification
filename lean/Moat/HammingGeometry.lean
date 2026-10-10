import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.SymmDiff

namespace BinaryFormMoat

section Neighborhoods

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

/-- Closed Hamming neighborhood in the full ambient product. -/
def hammingNeighborhood (r : ℕ) (A : Finset (∀ i, K i)) : Finset (∀ i, K i) :=
  Finset.univ.filter fun z => ∃ x ∈ A, hammingDist x z ≤ r

@[simp] theorem hammingNeighborhood_zero (A : Finset (∀ i, K i)) :
    hammingNeighborhood 0 A = A := by
  ext z
  simp [hammingNeighborhood, hammingDist_eq_zero]

theorem subset_hammingNeighborhood (r : ℕ) (A : Finset (∀ i, K i)) :
    A ⊆ hammingNeighborhood r A := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, by simp⟩

theorem hammingNeighborhood_mono_radius (r s : ℕ) (hrs : r ≤ s)
    (A : Finset (∀ i, K i)) : hammingNeighborhood r A ⊆ hammingNeighborhood s A := by
  intro z hz
  obtain ⟨x, hx, hdist⟩ := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hdist.trans hrs⟩

/-- The triangle inequality is enough for iterating lower bounds; no choice
of a shortest Hamming path is required. -/
theorem hammingNeighborhood_comp_subset (r s : ℕ) (A : Finset (∀ i, K i)) :
    hammingNeighborhood r (hammingNeighborhood s A) ⊆ hammingNeighborhood (s + r) A := by
  intro z hz
  obtain ⟨y, hy, hyz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hy).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx,
    (hammingDist_triangle x y z).trans (Nat.add_le_add hxy hyz)⟩

end Neighborhoods

/-- Boolean functions and their active-coordinate sets are equivalent. -/
def booleanSupportEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun x := Finset.univ.filter fun i => x i = true
  invFun s i := decide (i ∈ s)
  left_inv x := by funext i; cases hx : x i <;> simp [hx]
  right_inv s := by ext i; simp

/-- The support representation preserves Hamming distance exactly. -/
theorem support_symmDiff_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) :
    (symmDiff (booleanSupportEquiv ι x) (booleanSupportEquiv ι y)).card = hammingDist x y := by
  unfold hammingDist
  congr 1
  ext i
  cases hx : x i <;> cases hy : y i <;> simp [booleanSupportEquiv, Finset.mem_symmDiff, hx, hy]

/-- Numbering the coordinates gives the exact representation used by Harper.
For a prime batch with b bits per prime, the dimension is card(P)*b. -/
noncomputable def numberedSupportEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset (Fin (Fintype.card ι)) :=
  (booleanSupportEquiv ι).trans (Equiv.finsetCongr (Fintype.equivFin ι))

theorem numbered_support_symmDiff_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) :
    (symmDiff (numberedSupportEquiv ι x) (numberedSupportEquiv ι y)).card = hammingDist x y := by
  classical
  change (symmDiff ((booleanSupportEquiv ι x).map (Fintype.equivFin ι).toEmbedding)
    ((booleanSupportEquiv ι y).map (Fintype.equivFin ι).toEmbedding)).card = _
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding]
  rw [← Finset.image_symmDiff _ _ (Fintype.equivFin ι).injective,
    Finset.card_image_of_injective _ (Fintype.equivFin ι).injective]
  exact support_symmDiff_card x y

end BinaryFormMoat
