import Moat.RectanglePacking

namespace BinaryFormMoat

/-- An event fraction strictly below one yields one simultaneous slope choice
excluding every nonzero point of the rectangle. This is finite counting only. -/
theorem exists_rectangle_avoiding_root_assignment (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (hS : ∀ p : P, (S p).Nonempty) (A B : ℕ)
    (htail : ((rectangleWitnessEvent P S A B).card : ℝ) /
      Fintype.card (∀ p : P, S p) < 1) :
    ∃ σ : (∀ p : P, S p), ∀ z ∈ rectanglePoints A B, z ≠ (0, 0) →
      ∃ p : P, (z.1 : ZMod p.val) ≠ (σ p).val * (z.2 : ZMod p.val) := by
  classical
  have hchoices : Nonempty (∀ p : P, S p) := ⟨fun p =>
    ⟨Classical.choose (hS p), Classical.choose_spec (hS p)⟩⟩
  have hpos : (0 : ℝ) < Fintype.card (∀ p : P, S p) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hchoices
  have hlt : (rectangleWitnessEvent P S A B).card <
      (Finset.univ : Finset (∀ p : P, S p)).card := by
    rw [Finset.card_univ]
    exact_mod_cast (div_lt_one hpos).mp htail
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, fun z hz hzero => ?_⟩
  by_contra h
  apply hσ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, z, hz, hzero, fun p => ?_⟩
  by_contra hp
  exact h ⟨p, hp⟩

end BinaryFormMoat
