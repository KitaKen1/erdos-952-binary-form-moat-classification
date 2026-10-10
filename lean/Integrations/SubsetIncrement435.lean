import Integrations.SubsetSampling435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Average of fixed-subset quantities. Subset selection is outside the experiment. -/
def subsetMean {ι : Type*} [Fintype ι] (s : ℕ) (f : Finset ι → ℝ) : ℝ := by
  classical
  exact (∑ A ∈ (Finset.univ : Finset ι).powersetCard s, f A) /
    ((Finset.univ : Finset ι).powersetCard s).card

/-- The exact insertion/erasure bijection for sampling without replacement. -/
theorem sum_subset_insert_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (g : Finset ι → ι → ℝ) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
      ∑ j ∈ Finset.univ \ A, g A j) =
    ∑ B ∈ (Finset.univ : Finset ι).powersetCard (s + 1), ∑ j ∈ B, g (B.erase j) j := by
  classical
  let L := (((Finset.univ : Finset ι).powersetCard s) ×ˢ Finset.univ).filter
    (fun p => p.2 ∉ p.1)
  let R := (((Finset.univ : Finset ι).powersetCard (s + 1)) ×ˢ Finset.univ).filter
    (fun p => p.2 ∈ p.1)
  have hL : ∀ p : Finset ι × ι, p ∈ L ↔
      p.1 ∈ (Finset.univ : Finset ι).powersetCard s ∧ p.2 ∈ Finset.univ \ p.1 := by
    intro p
    simp [L]
  have hR : ∀ p : Finset ι × ι, p ∈ R ↔
      p.1 ∈ (Finset.univ : Finset ι).powersetCard (s + 1) ∧ p.2 ∈ p.1 := by
    intro p
    simp [R]
  rw [← Finset.sum_finset_product L _ _ hL (f := fun p => g p.1 p.2),
    ← Finset.sum_finset_product R _ _ hR (f := fun p => g (p.1.erase p.2) p.2)]
  refine Finset.sum_nbij' (fun p => (insert p.2 p.1, p.2))
    (fun p => (p.1.erase p.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases (hL p).mp hp with ⟨hp, hj⟩
    have hn := (Finset.mem_sdiff.mp hj).2
    apply (hR _).mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hn,
        (Finset.mem_powersetCard.mp hp).2]⟩
    · exact Finset.mem_insert_self _ _
  · intro p hp
    rcases (hR p).mp hp with ⟨hp, hj⟩
    apply (hL _).mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hj,
        (Finset.mem_powersetCard.mp hp).2]; omega⟩
    · simp
  · intro p hp
    have hn := (Finset.mem_sdiff.mp ((hL p).mp hp).2).2
    simp [hn]
  · intro p hp
    have hj := ((hR p).mp hp).2
    simp [Finset.insert_erase hj]
  · intro p hp
    have hn := (Finset.mem_sdiff.mp ((hL p).mp hp).2).2
    simp [hn]

/-- Successive subset-size averages have the exact fresh-coordinate increment. -/
theorem subsetMean_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : s < Fintype.card ι) (f : Finset ι → ℝ) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
      ∑ j ∈ Finset.univ \ A, (f (insert j A) - f A)) /
      (((Finset.univ : Finset ι).powersetCard s).card * (Fintype.card ι - s : ℕ) : ℕ) =
        subsetMean (s + 1) f - subsetMean s f := by
  classical
  let C := (Finset.univ : Finset ι).powersetCard s
  let E := (Finset.univ : Finset ι).powersetCard (s + 1)
  have hC : (C.card : ℝ) ≠ 0 := by
    simp only [C, Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt hs)).ne'
  have hE : (E.card : ℝ) ≠ 0 := by
    simp only [E, Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast (Nat.choose_pos (by omega : s + 1 ≤ Fintype.card ι)).ne'
  have hk : ((Fintype.card ι - s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hs).ne'
  have hcard : (C.card : ℝ) * (Fintype.card ι - s : ℕ) = (s + 1 : ℕ) * (E.card : ℝ) := by
    have h : Nat.choose (Fintype.card ι) s * (Fintype.card ι - s) =
        (s + 1) * Nat.choose (Fintype.card ι) (s + 1) := by
      rw [← Nat.choose_succ_right_eq, Nat.mul_comm]
    simp only [C, E, Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast h
  have hins : (∑ A ∈ C, ∑ j ∈ Finset.univ \ A, f (insert j A)) =
      (s + 1 : ℕ) * ∑ B ∈ E, f B := by
    rw [sum_subset_insert_erase]
    calc
      _ = ∑ B ∈ E, (s + 1 : ℕ) * f B := by
        apply Finset.sum_congr rfl
        intro B hB
        have hBcard := (Finset.mem_powersetCard.mp hB).2
        calc
          _ = ∑ _j ∈ B, f B := Finset.sum_congr rfl (fun j hj => by rw [Finset.insert_erase hj])
          _ = _ := by simp [hBcard]
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hbase : (∑ A ∈ C, ∑ _j ∈ Finset.univ \ A, f A) =
      (Fintype.card ι - s : ℕ) * ∑ A ∈ C, f A := by
    calc
      _ = ∑ A ∈ C, (Fintype.card ι - s : ℕ) * f A := by
        apply Finset.sum_congr rfl
        intro A hA
        have hAcard := (Finset.mem_powersetCard.mp hA).2
        simp [Finset.card_sdiff_of_subset (Finset.subset_univ A), hAcard]
      _ = _ := (Finset.mul_sum _ _ _).symm
  change (∑ A ∈ C, ∑ j ∈ Finset.univ \ A, (f (insert j A) - f A)) /
    ((C.card * (Fintype.card ι - s) : ℕ) : ℝ) = _
  simp only [Finset.sum_sub_distrib, hins, hbase, Nat.cast_mul]
  change _ = (∑ B ∈ E, f B) / (E.card : ℝ) - (∑ A ∈ C, f A) / (C.card : ℝ)
  have hsucc : (s + 1 : ℝ) ≠ 0 := by positivity
  push_cast at hcard ⊢
  field_simp
  linear_combination -(∑ B ∈ E, f B) * hcard

/-- Diminishing returns implies the deletion form of Han's inequality. -/
theorem sum_erase_marginals_le {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℝ)
    (h : ∀ A B : Finset ι, A ⊆ B → ∀ j, j ∉ B →
      f (insert j B) - f B ≤ f (insert j A) - f A) (B : Finset ι) :
    (∑ j ∈ B, (f B - f (B.erase j))) ≤ f B - f ∅ := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
    rw [Finset.sum_insert hi]
    have hj : ∀ j ∈ B,
        f (insert i B) - f ((insert i B).erase j) ≤ f B - f (B.erase j) := by
      intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hi hj
      have hp := h (B.erase j) ((insert i B).erase j)
        (Finset.erase_subset_erase j (Finset.subset_insert i B)) j (Finset.notMem_erase j _)
      rw [Finset.insert_erase (Finset.mem_insert_of_mem hj), Finset.insert_erase hj] at hp
      exact hp
    have hh := (Finset.sum_le_sum hj).trans ih
    rw [Finset.erase_insert hi]
    linarith

/-- The precise bound needed by enrichment; full concavity machinery is unnecessary. -/
theorem subsetMean_forward_increment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 0 < s) (hsk : s < Fintype.card ι) (f : Finset ι → ℝ)
    (hf : f ∅ = 0)
    (h : ∀ A B : Finset ι, A ⊆ B → ∀ j, j ∉ B →
      f (insert j B) - f B ≤ f (insert j A) - f A) :
    subsetMean (s + 1) f - subsetMean s f ≤ subsetMean s f / s := by
  classical
  let E := (Finset.univ : Finset ι).powersetCard (s + 1)
  have hE : (E.card : ℝ) > 0 := by
    simp only [E, Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast Nat.choose_pos (by omega : s + 1 ≤ Fintype.card ι)
  have hsum : (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
      ∑ j ∈ Finset.univ \ A, (f (insert j A) - f A)) ≤ ∑ B ∈ E, f B := by
    rw [sum_subset_insert_erase]
    apply Finset.sum_le_sum
    intro B hB
    have he : (∑ j ∈ B, (f (insert j (B.erase j)) - f (B.erase j))) =
        ∑ j ∈ B, (f B - f (B.erase j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.insert_erase hj]
    rw [he]
    simpa [hf] using sum_erase_marginals_le f h B
  have hinc := subsetMean_increment s hsk f
  have hcard : ((((Finset.univ : Finset ι).powersetCard s).card : ℝ) *
      (Fintype.card ι - s : ℕ)) = (s + 1 : ℕ) * (E.card : ℝ) := by
    simp only [E, Finset.card_powersetCard, Finset.card_univ]
    have h : Nat.choose (Fintype.card ι) s * (Fintype.card ι - s) =
        (s + 1) * Nat.choose (Fintype.card ι) (s + 1) := by
      rw [← Nat.choose_succ_right_eq, Nat.mul_comm]
    exact_mod_cast h
  have hden : (0 : ℝ) <
      ((((Finset.univ : Finset ι).powersetCard s).card * (Fintype.card ι - s) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hcard]
    positivity
  have hb := (div_le_div_of_nonneg_right hsum (le_of_lt hden))
  rw [hinc] at hb
  have he : (∑ B ∈ E, f B) = (E.card : ℝ) * subsetMean (s + 1) f := by
    unfold subsetMean
    change _ = (E.card : ℝ) * ((∑ B ∈ E, f B) / E.card)
    field_simp
  rw [he, Nat.cast_mul, hcard] at hb
  have hnorm : (E.card : ℝ) * subsetMean (s + 1) f /
      ((s + 1 : ℕ) * (E.card : ℝ)) = subsetMean (s + 1) f / (s + 1 : ℕ) := by
    field_simp
  rw [hnorm] at hb
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htR : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  have hh := (le_div_iff₀ htR).mp hb
  apply (le_div_iff₀ hsR).mpr
  push_cast at hh
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.subsetMean
#print axioms BinaryFormMoat.EntropyIntegration.sum_subset_insert_erase
#print axioms BinaryFormMoat.EntropyIntegration.subsetMean_increment
#print axioms BinaryFormMoat.EntropyIntegration.sum_erase_marginals_le
#print axioms BinaryFormMoat.EntropyIntegration.subsetMean_forward_increment_le
