import LeanPool.BooleanIsoperimetry.Harper
import Moat.HammingGeometry

namespace BinaryFormMoat.HarperIntegration

open BooleanIsoperimetry

/-- The complete neighborhood, including points outside an encoded acceptance
set, is preserved by the Boolean-function/set representation change. -/
theorem numbered_neighborhood {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (A : Finset (ι → Bool)) :
    (hammingNeighborhood r A).map (numberedSupportEquiv ι).toEmbedding =
      neighborhood r (A.map (numberedSupportEquiv ι).toEmbedding) := by
  classical
  ext z
  obtain ⟨x, rfl⟩ := (numberedSupportEquiv ι).surjective z
  constructor
  · intro hz
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hz
    have he : y = x := (numberedSupportEquiv ι).injective hxy
    subst y
    obtain ⟨a, ha, hax⟩ := (Finset.mem_filter.mp hy).2
    apply mem_neighborhood_iff.mpr
    refine ⟨numberedSupportEquiv ι a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    simpa only [hDist, numbered_support_symmDiff_card] using hax
  · intro hz
    obtain ⟨u, hu, hux⟩ := mem_neighborhood_iff.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    apply Finset.mem_map.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, ?_⟩, rfl⟩
    simpa only [hDist, Equiv.coe_toEmbedding, numbered_support_symmDiff_card] using hux

/-- Harper's radius-one theorem now applies directly to the core's Boolean
functions on any finite coordinate type, including prime/bit pairs. -/
theorem harper_hamming_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) :
    H (Fintype.card ι) A.card ≤ (hammingNeighborhood 1 A).card := by
  have h := harper_theorem (Fintype.card ι)
    (A.map (numberedSupportEquiv ι).toEmbedding) A.card (Finset.card_map _)
  change H (Fintype.card ι) A.card ≤ _ at h
  rw [← numbered_neighborhood, Finset.card_map] at h
  exact h

/-- A single radius-one isoperimetric theorem supplies every radius. The
explicit recurrence H^[r] is an unconditional numerical lower bound. -/
theorem harper_hamming_iterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) (r : ℕ) :
    (H (Fintype.card ι))^[r] A.card ≤ (hammingNeighborhood r A).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (H_mono ih).trans ((harper_hamming_one (hammingNeighborhood r A)).trans
      (Finset.card_le_card (hammingNeighborhood_comp_subset 1 r A)))

end BinaryFormMoat.HarperIntegration
