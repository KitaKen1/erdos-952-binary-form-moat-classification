import Integrations.SubsetIncrement435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Count a uniform inner subset through every uniform containing batch. -/
theorem sum_nested_subsets {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b q : ℕ) (hbq : b ≤ q) (f : Finset ι → ℝ) :
    (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q, ∑ S ∈ Q.powersetCard b, f S) =
      Nat.choose (Fintype.card ι - b) (q - b) *
        ∑ S ∈ (Finset.univ : Finset ι).powersetCard b, f S := by
  classical
  have hfilter : ∀ Q : Finset ι,
      Q.powersetCard b = ((Finset.univ : Finset ι).powersetCard b).filter (fun S => S ⊆ Q) := by
    intro Q
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    exact and_comm
  have hinner : ∀ Q : Finset ι, (∑ S ∈ Q.powersetCard b, f S) =
      ∑ S ∈ (Finset.univ : Finset ι).powersetCard b, if S ⊆ Q then f S else 0 := by
    intro Q
    rw [hfilter, Finset.sum_filter]
  simp_rw [hinner]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← Finset.sum_filter]
  have hc := Finset.card_filter_powersetCard_subset S Finset.univ q
    (Finset.subset_univ _) (by rw [(Finset.mem_powersetCard.mp hS).2]; exact hbq)
  simp only [Finset.card_univ, (Finset.mem_powersetCard.mp hS).2] at hc
  simp [hc]

/-- Uniform q-batch followed by a uniform b-subset has the uniform b-subset marginal. -/
theorem nested_subsetMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b q : ℕ) (hbq : b ≤ q) (hqk : q ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      (∑ S ∈ Q.powersetCard b, f S) / (Q.powersetCard b).card) /
      ((Finset.univ : Finset ι).powersetCard q).card = subsetMean b f := by
  classical
  have hb : ((Nat.choose (Fintype.card ι) b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hbq.trans hqk)).ne'
  have hq : ((Nat.choose (Fintype.card ι) q : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hqk).ne'
  have hqb : ((Nat.choose q b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hbq).ne'
  have hinner : (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      (∑ S ∈ Q.powersetCard b, f S) / (Q.powersetCard b).card) =
      (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
        ∑ S ∈ Q.powersetCard b, f S) / Nat.choose q b := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [Finset.card_powersetCard, (Finset.mem_powersetCard.mp hQ).2]
  rw [hinner, sum_nested_subsets b q hbq]
  simp only [subsetMean, Finset.card_powersetCard, Finset.card_univ]
  have hc : (Nat.choose (Fintype.card ι) q : ℝ) * Nat.choose q b =
      Nat.choose (Fintype.card ι) b * Nat.choose (Fintype.card ι - b) (q - b) := by
    exact_mod_cast Nat.choose_mul (n := Fintype.card ι) hbq
  field_simp
  linear_combination -(∑ S ∈ (Finset.univ : Finset ι).powersetCard b, f S) * hc

/-- The previous marginal remains exact when global independent labels are preselected. -/
theorem nested_labelled_subsetMean_eq {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (b q : ℕ) (hbq : b ≤ q) (hqk : q ≤ Fintype.card ι)
    (f : Finset ι → (ι → R) → ℝ) :
    (∑ ρ : ι → R,
      (∑ Q ∈ (Finset.univ : Finset ι).powersetCard q,
        (∑ S ∈ Q.powersetCard b, f S ρ) / (Q.powersetCard b).card) /
        ((Finset.univ : Finset ι).powersetCard q).card) / Fintype.card (ι → R) =
      subsetLabelAverage b f := by
  classical
  simp_rw [nested_subsetMean_eq b q hbq hqk, subsetMean]
  simp only [subsetLabelAverage, Finset.sum_div, div_div]
  rw [Finset.sum_comm]
  simp only [mul_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr (by ext; simp)
  intro ρ _
  congr 5
  exact Subsingleton.elim _ _

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.sum_nested_subsets
#print axioms BinaryFormMoat.EntropyIntegration.nested_subsetMean_eq
#print axioms BinaryFormMoat.EntropyIntegration.nested_labelled_subsetMean_eq
