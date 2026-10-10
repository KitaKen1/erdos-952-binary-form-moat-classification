import Integrations.EmpiricalLists435

namespace BinaryFormMoat.EntropyIntegration

def translationOverlap {G : Type*} [Fintype G] [DecidableEq G] [Add G]
    (K E : Finset G) (x : G) : ℕ := (E.filter (fun h => x + h ∈ K)).card

theorem sum_translate_hits {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (K : Finset G) (h : G) :
    (∑ x : G, if x + h ∈ K then (1 : ℕ) else 0) = K.card := by
  classical
  have he := Equiv.sum_comp (Equiv.addRight h) (fun x => if x ∈ K then (1 : ℕ) else 0)
  change (∑ x, if x + h ∈ K then (1 : ℕ) else 0) =
    ∑ x, if x ∈ K then (1 : ℕ) else 0 at he
  simpa using he

/-- Translation double counting works in every finite additive group. -/
theorem sum_translationOverlap {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (K E : Finset G) : (∑ x, translationOverlap K E x) = K.card * E.card := by
  classical
  simp only [translationOverlap, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [sum_translate_hits]
  simp [Nat.mul_comm]

noncomputable def overlapExceptionalCandidates {G : Type*} [Fintype G]
    [DecidableEq G] [Add G] (K E : Finset G) (δ : ℝ) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => δ * K.card < (translationOverlap K E x : ℝ))

theorem overlap_le_of_not_exceptional {G : Type*} [Fintype G] [DecidableEq G] [Add G]
    (K E : Finset G) (δ : ℝ) (x : G) (hx : x ∉ overlapExceptionalCandidates K E δ) :
    (translationOverlap K E x : ℝ) ≤ δ * K.card := by
  classical
  simpa [overlapExceptionalCandidates, not_lt] using hx

/-- At most |E|/delta candidates have excessive overlap with E. -/
theorem overlapExceptionalCandidates_card_le {G : Type*} [Fintype G] [DecidableEq G]
    [AddGroup G] (K E : Finset G) (hK : K.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ((overlapExceptionalCandidates K E δ).card : ℝ) ≤ (E.card : ℝ) / δ := by
  classical
  have hk : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hsum : δ * K.card * (overlapExceptionalCandidates K E δ).card ≤
      (K.card : ℝ) * E.card := by
    calc
      _ = ∑ x ∈ overlapExceptionalCandidates K E δ, δ * K.card := by simp [mul_comm]
      _ ≤ ∑ x ∈ overlapExceptionalCandidates K E δ, (translationOverlap K E x : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (show δ * K.card < (translationOverlap K E x : ℝ) from
          (Finset.mem_filter.mp hx).2).le
      _ ≤ ∑ x : G, (translationOverlap K E x : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ = _ := by exact_mod_cast sum_translationOverlap K E
  apply (le_div_iff₀ hδ).mpr
  nlinarith

/-- A probability floor outside E gives a translated hit-probability floor.
This deterministic step precedes the conditional independent-trial tail. -/
theorem translated_hit_probability_lower {G : Type*} [Fintype G] [DecidableEq G]
    [AddGroup G] (K E : Finset G) (x : G) (w : G → ℝ) (α : ℝ)
    (hw : ∀ h, 0 ≤ w h) (hfloor : ∀ h ∉ E, α ≤ w h) :
    α * ((K.card : ℝ) - translationOverlap K E x) ≤
      ∑ h, if x + h ∈ K then w h else 0 := by
  classical
  let H : Finset G := Finset.univ.filter (fun h => x + h ∈ K)
  have hH : H.card = K.card := by
    have he := Equiv.sum_comp (Equiv.addLeft x) (fun h => if h ∈ K then (1 : ℕ) else 0)
    change (∑ h, if x + h ∈ K then (1 : ℕ) else 0) =
      ∑ h, if h ∈ K then (1 : ℕ) else 0 at he
    simpa [H] using he
  have hHE : (H ∩ E).card = translationOverlap K E x := by
    congr 1
    ext h
    simp [H, and_comm]
  have hc : ((H \ E).card : ℝ) = (K.card : ℝ) - translationOverlap K E x := by
    have hn := Finset.card_sdiff_add_card_inter H E
    rw [hH, hHE] at hn
    have hn' : ((H \ E).card : ℝ) + translationOverlap K E x = K.card := by exact_mod_cast hn
    linarith
  calc
    _ = ∑ h ∈ H \ E, α := by rw [← hc]; simp [mul_comm]
    _ ≤ ∑ h ∈ H \ E, w h := Finset.sum_le_sum (fun h hh =>
      hfloor h (Finset.mem_sdiff.mp hh).2)
    _ ≤ ∑ h ∈ H, w h := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun h _ _ => hw h)
    _ = _ := by rw [Finset.sum_filter]

theorem translated_hit_probability_lower_of_overlap {G : Type*} [Fintype G]
    [DecidableEq G] [AddGroup G] (K E : Finset G) (x : G) (w : G → ℝ)
    (α δ : ℝ) (hα : 0 ≤ α) (hw : ∀ h, 0 ≤ w h)
    (hfloor : ∀ h ∉ E, α ≤ w h)
    (hoverlap : (translationOverlap K E x : ℝ) ≤ δ * K.card) :
    α * (1 - δ) * K.card ≤ ∑ h, if x + h ∈ K then w h else 0 := by
  have h := translated_hit_probability_lower K E x w α hw hfloor
  have hm := mul_le_mul_of_nonneg_left hoverlap hα
  nlinarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.sum_translate_hits
#print axioms BinaryFormMoat.EntropyIntegration.sum_translationOverlap
#print axioms BinaryFormMoat.EntropyIntegration.overlap_le_of_not_exceptional
#print axioms BinaryFormMoat.EntropyIntegration.overlapExceptionalCandidates_card_le
#print axioms BinaryFormMoat.EntropyIntegration.translated_hit_probability_lower
#print axioms BinaryFormMoat.EntropyIntegration.translated_hit_probability_lower_of_overlap
