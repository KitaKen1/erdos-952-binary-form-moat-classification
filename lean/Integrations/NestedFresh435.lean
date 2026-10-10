import Integrations.NestedSubset435
import Integrations.DisjointSubset435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Insert/erase reindexing inside an arbitrary fixed outer batch. -/
theorem sum_subset_insert_erase_within {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (b : ℕ) (w : Finset ι → ι → ℝ) :
    (∑ S ∈ C.powersetCard b, ∑ j ∈ C \ S, w S j) =
      ∑ B ∈ C.powersetCard (b + 1), ∑ j ∈ B, w (B.erase j) j := by
  classical
  let L := ((C.powersetCard b) ×ˢ C).filter (fun p => p.2 ∉ p.1)
  let R := ((C.powersetCard (b + 1)) ×ˢ C).filter (fun p => p.2 ∈ p.1)
  have hL : ∀ p : Finset ι × ι, p ∈ L ↔
      p.1 ∈ C.powersetCard b ∧ p.2 ∈ C \ p.1 := by
    intro p
    simp [L, and_assoc]
  have hR : ∀ p : Finset ι × ι, p ∈ R ↔
      p.1 ∈ C.powersetCard (b + 1) ∧ p.2 ∈ p.1 := by
    intro p
    simp only [R, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hB, _⟩, hj⟩
      exact ⟨hB, hj⟩
    · rintro ⟨hB, hj⟩
      exact ⟨⟨hB, (Finset.mem_powersetCard.mp hB).1 hj⟩, hj⟩
  rw [← Finset.sum_finset_product L _ _ hL (f := fun p => w p.1 p.2),
    ← Finset.sum_finset_product R _ _ hR (f := fun p => w (p.1.erase p.2) p.2)]
  refine Finset.sum_nbij' (fun p => (insert p.2 p.1, p.2))
    (fun p => (p.1.erase p.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases (hL p).mp hp with ⟨hS, hj⟩
    rcases Finset.mem_sdiff.mp hj with ⟨hjC, hjS⟩
    apply (hR _).mpr
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset hjC (Finset.mem_powersetCard.mp hS).1,
        by rw [Finset.card_insert_of_notMem hjS, (Finset.mem_powersetCard.mp hS).2]⟩,
      Finset.mem_insert_self _ _⟩
  · intro p hp
    rcases (hR p).mp hp with ⟨hB, hj⟩
    apply (hL _).mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.Subset.trans (Finset.erase_subset _ _) (Finset.mem_powersetCard.mp hB).1,
        by rw [Finset.card_erase_of_mem hj, (Finset.mem_powersetCard.mp hB).2]; omega⟩
    · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powersetCard.mp hB).1 hj, by simp⟩
  · intro p hp
    have hn := (Finset.mem_sdiff.mp ((hL p).mp hp).2).2
    simp [hn]
  · intro p hp
    have hj := ((hR p).mp hp).2
    simp [Finset.insert_erase hj]
  · intro p hp
    have hn := (Finset.mem_sdiff.mp ((hL p).mp hp).2).2
    simp [hn]

/-- Weighted count of (outer batch, prefix, fresh coordinate), keeping both
prefix and coordinate dependence in the summand. -/
theorem sum_nested_fresh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b q : ℕ) (hbq : b < q) (w : Finset ι → ι → ℝ) :
    (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      ∑ S ∈ Q.powersetCard b, ∑ j ∈ Q \ S, w S j) =
      Nat.choose (Fintype.card ι - (b + 1)) (q - (b + 1)) *
        ∑ S ∈ (Finset.univ : Finset ι).powersetCard b,
          ∑ j ∈ Finset.univ \ S, w S j := by
  classical
  simp_rw [sum_subset_insert_erase_within]
  rw [sum_nested_subsets (b + 1) q (by omega),
    ← sum_subset_insert_erase]

/-- Exact normalization for a prefix/fresh-coordinate pair in a random batch. -/
theorem choose_nested_fresh_identity (k b q : ℕ) (hbq : b < q) :
    Nat.choose k q * Nat.choose q b * (q - b) =
      Nat.choose (k - (b + 1)) (q - (b + 1)) * Nat.choose k b * (k - b) := by
  have hq := Nat.choose_succ_right_eq q b
  have hk := Nat.choose_succ_right_eq k b
  have hc := Nat.choose_mul (n := k) (show b + 1 ≤ q by omega)
  calc
    _ = Nat.choose k q * (Nat.choose q (b + 1) * (b + 1)) := by rw [hq]; ring
    _ = (Nat.choose k q * Nat.choose q (b + 1)) * (b + 1) := by ring
    _ = (Nat.choose k (b + 1) * Nat.choose (k - (b + 1)) (q - (b + 1))) * (b + 1) := by rw [hc]
    _ = Nat.choose (k - (b + 1)) (q - (b + 1)) * (Nat.choose k (b + 1) * (b + 1)) := by ring
    _ = _ := by rw [hk]; ring

/-- Uniform outer batch, uniform inner prefix and uniform fresh coordinate
have the same (prefix,coordinate) marginal as sampling globally. -/
theorem nested_fresh_mean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b q : ℕ) (hbq : b < q) (hqk : q ≤ Fintype.card ι) (w : Finset ι → ι → ℝ) :
    relativeSubsetMean (Finset.univ : Finset ι) q (fun Q =>
      relativeSubsetMean Q b (fun S => (∑ j ∈ Q \ S, w S j) / (q - b : ℕ))) =
      subsetMean b (fun S => (∑ j ∈ Finset.univ \ S, w S j) / (Fintype.card ι - b : ℕ)) := by
  classical
  have hinner : ∀ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      relativeSubsetMean Q b (fun S => (∑ j ∈ Q \ S, w S j) / (q - b : ℕ)) =
        (∑ S ∈ Q.powersetCard b, ∑ j ∈ Q \ S, w S j) /
          ((Nat.choose q b : ℝ) * (q - b : ℕ)) := by
    intro Q hQ
    simp only [relativeSubsetMean, ← Finset.sum_div, div_div,
      Finset.card_powersetCard, (Finset.mem_powersetCard.mp hQ).2, mul_comm]
  change (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
    relativeSubsetMean Q b (fun S => (∑ j ∈ Q \ S, w S j) / (q - b : ℕ))) /
      ((Finset.univ : Finset ι).powersetCard q).card = _
  have he : (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      relativeSubsetMean Q b (fun S => (∑ j ∈ Q \ S, w S j) / (q - b : ℕ))) =
      ∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
        (∑ S ∈ Q.powersetCard b, ∑ j ∈ Q \ S, w S j) /
          ((Nat.choose q b : ℝ) * (q - b : ℕ)) :=
    Finset.sum_congr rfl (fun Q hQ => hinner Q hQ)
  rw [he]
  rw [← Finset.sum_div, sum_nested_fresh b q hbq]
  simp only [subsetMean, Finset.card_powersetCard, Finset.card_univ,
    ← Finset.sum_div, div_div]
  have hc : (Nat.choose (Fintype.card ι) q : ℝ) * Nat.choose q b * (q - b : ℕ) =
      Nat.choose (Fintype.card ι - (b + 1)) (q - (b + 1)) *
        Nat.choose (Fintype.card ι) b * (Fintype.card ι - b : ℕ) := by
    exact_mod_cast choose_nested_fresh_identity (Fintype.card ι) b q hbq
  have hCq : (Nat.choose (Fintype.card ι) q : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hqk).ne'
  have hCqb : (Nat.choose q b : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : b ≤ q)).ne'
  have hCb : (Nat.choose (Fintype.card ι) b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : b ≤ Fintype.card ι)).ne'
  have hqb : ((q - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hbq).ne'
  have hkb : ((Fintype.card ι - b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt (by omega : b < Fintype.card ι)).ne'
  field_simp
  linear_combination -(∑ S ∈ (Finset.univ : Finset ι).powersetCard b,
    ∑ j ∈ Finset.univ \ S, w S j) * hc

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.sum_subset_insert_erase_within
#print axioms BinaryFormMoat.EntropyIntegration.sum_nested_fresh
#print axioms BinaryFormMoat.EntropyIntegration.choose_nested_fresh_identity
#print axioms BinaryFormMoat.EntropyIntegration.nested_fresh_mean_eq
