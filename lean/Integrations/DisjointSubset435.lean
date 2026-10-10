import Integrations.LabelledSubsetEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Uniform fixed-size subset of a specified ambient finite set. -/
def relativeSubsetMean {ι : Type*} (C : Finset ι) (r : ℕ) (f : Finset ι → ℝ) : ℝ :=
  (∑ J ∈ C.powersetCard r, f J) / (C.powersetCard r).card

theorem relativeSubsetMean_mono {ι : Type*} (C : Finset ι) (r : ℕ)
    (f g : Finset ι → ℝ) (h : ∀ J ∈ C.powersetCard r, f J ≤ g J) :
    relativeSubsetMean C r f ≤ relativeSubsetMean C r g := by
  unfold relativeSubsetMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

theorem relativeSubsetMean_const {ι : Type*} (C : Finset ι) (r : ℕ)
    (hr : r ≤ C.card) (c : ℝ) : relativeSubsetMean C r (fun _ => c) = c := by
  have hc : ((C.powersetCard r).card : ℝ) ≠ 0 := by
    rw [Finset.card_powersetCard]
    exact_mod_cast (Nat.choose_pos hr).ne'
  simp only [relativeSubsetMean, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

theorem relativeSubsetMean_sub {ι : Type*} (C : Finset ι) (r : ℕ)
    (f g : Finset ι → ℝ) : relativeSubsetMean C r (fun J => f J - g J) =
      relativeSubsetMean C r f - relativeSubsetMean C r g := by
  simp only [relativeSubsetMean, Finset.sum_sub_distrib, sub_div]

/-- Exact double counting of ordered disjoint subsets, with any weights. -/
theorem sum_disjoint_subsets_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b r : ℕ) (f : Finset ι → Finset ι → ℝ) :
    (∑ S ∈ (Finset.univ : Finset ι).powersetCard b,
      ∑ J ∈ (Finset.univ \ S).powersetCard r, f S J) =
    ∑ J ∈ (Finset.univ : Finset ι).powersetCard r,
      ∑ S ∈ (Finset.univ \ J).powersetCard b, f S J := by
  classical
  have he (S : Finset ι) (n : ℕ) :
      (Finset.univ \ S).powersetCard n =
        ((Finset.univ : Finset ι).powersetCard n).filter (fun J => Disjoint S J) := by
    ext J
    simp [Finset.mem_powersetCard, Finset.subset_sdiff, disjoint_comm, and_comm]
  simp_rw [he, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [disjoint_comm]

/-- Disjoint subset cardinalities have the exact symmetric normalization. -/
theorem choose_disjoint_card_identity (k b r : ℕ) (_h : b + r ≤ k) :
    Nat.choose k b * Nat.choose (k - b) r = Nat.choose k r * Nat.choose (k - r) b := by
  have hb : b ≤ b + r := by omega
  have hr : r ≤ b + r := by omega
  have h1 := Nat.choose_mul (n := k) hb
  have h2 := Nat.choose_mul (n := k) hr
  have hs : Nat.choose (b + r) b = Nat.choose (b + r) r := Nat.choose_symm_add
  have he1 : b + r - b = r := by omega
  have he2 : b + r - r = b := by omega
  rw [he1] at h1
  rw [he2] at h2
  rw [hs] at h1
  exact h1.symm.trans h2

/-- Choosing b coordinates and then r distinct remaining coordinates leaves
an exactly uniform r-subset marginal. -/
theorem disjoint_subsetMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b r : ℕ) (hbr : b + r ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    subsetMean b (fun S => relativeSubsetMean (Finset.univ \ S) r f) = subsetMean r f := by
  classical
  have hb : b ≤ Fintype.card ι := by omega
  have hr : r ≤ Fintype.card ι := by omega
  have hrem : r ≤ Fintype.card ι - b := by omega
  have hCb : (Nat.choose (Fintype.card ι) b : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hb).ne'
  have hCr : (Nat.choose (Fintype.card ι) r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have hR : (Nat.choose (Fintype.card ι - b) r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hrem).ne'
  have hinner : (∑ S ∈ (Finset.univ : Finset ι).powersetCard b,
      relativeSubsetMean (Finset.univ \ S) r f) =
      (∑ S ∈ (Finset.univ : Finset ι).powersetCard b,
        ∑ J ∈ (Finset.univ \ S).powersetCard r, f J) /
          Nat.choose (Fintype.card ι - b) r := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [relativeSubsetMean, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      (Finset.mem_powersetCard.mp hS).2]
  unfold subsetMean
  rw [hinner, sum_disjoint_subsets_comm]
  have hsum : (∑ J ∈ (Finset.univ : Finset ι).powersetCard r,
      ∑ _S ∈ (Finset.univ \ J).powersetCard b, f J) =
      Nat.choose (Fintype.card ι - r) b * ∑ J ∈ (Finset.univ : Finset ι).powersetCard r, f J := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ,
      (Finset.mem_powersetCard.mp hJ).2]
  rw [hsum]
  simp only [Finset.card_powersetCard, Finset.card_univ]
  have hc : (Nat.choose (Fintype.card ι) b : ℝ) * Nat.choose (Fintype.card ι - b) r =
      Nat.choose (Fintype.card ι) r * Nat.choose (Fintype.card ι - r) b := by
    exact_mod_cast choose_disjoint_card_identity (Fintype.card ι) b r hbr
  field_simp
  linear_combination -(∑ J ∈ (Finset.univ : Finset ι).powersetCard r, f J) * hc

/-- Average over ordered disjoint subsets and independent preselected labels. -/
def disjointLabelAverage {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (b r : ℕ) (f : Finset ι → Finset ι → (ι → R) → ℝ) : ℝ :=
  subsetLabelAverage b (fun S ρ => relativeSubsetMean (Finset.univ \ S) r (fun J => f S J ρ))

theorem disjointLabelAverage_mono {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (b r : ℕ) (f g : Finset ι → Finset ι → (ι → R) → ℝ)
    (h : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b,
      ∀ J ∈ (Finset.univ \ S).powersetCard r, ∀ ρ, f S J ρ ≤ g S J ρ) :
    disjointLabelAverage b r f ≤ disjointLabelAverage b r g := by
  classical
  apply subsetLabelAverage_mono
  intro S hS ρ
  exact relativeSubsetMean_mono _ r _ _ (fun J hJ => h S hS J hJ ρ)

theorem disjointLabelAverage_ignore_prefix {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (b r : ℕ) (hbr : b + r ≤ Fintype.card ι) (f : Finset ι → (ι → R) → ℝ) :
    disjointLabelAverage b r (fun _ J ρ => f J ρ) = subsetLabelAverage r f := by
  classical
  unfold disjointLabelAverage
  simp_rw [subsetLabelAverage_eq_mean_subsetMean]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  exact disjoint_subsetMean_eq b r hbr (fun J => f J ρ)

theorem disjointLabelAverage_const {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R] (b r : ℕ)
    (hbr : b + r ≤ Fintype.card ι) (c : ℝ) :
    disjointLabelAverage (ι := ι) (R := R) b r (fun _ _ _ => c) = c := by
  classical
  have hinner : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b,
      relativeSubsetMean (Finset.univ \ S) r (fun _ => c) = c := by
    intro S hS
    apply relativeSubsetMean_const
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      (Finset.mem_powersetCard.mp hS).2]
    omega
  have he : disjointLabelAverage (ι := ι) (R := R) b r (fun _ _ _ => c) =
      subsetLabelAverage (ι := ι) (R := R) b (fun _ _ => c) := by
    unfold disjointLabelAverage subsetLabelAverage
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    simp only [hinner S hS]
  rw [he, subsetLabelAverage_const b (by omega)]

theorem disjointLabelAverage_sub {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (b r : ℕ) (f g : Finset ι → Finset ι → (ι → R) → ℝ) :
    disjointLabelAverage b r (fun S J ρ => f S J ρ - g S J ρ) =
      disjointLabelAverage b r f - disjointLabelAverage b r g := by
  classical
  simp only [disjointLabelAverage, relativeSubsetMean_sub, subsetLabelAverage_sub]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean
#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_mono
#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_const
#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_sub
#print axioms BinaryFormMoat.EntropyIntegration.sum_disjoint_subsets_comm
#print axioms BinaryFormMoat.EntropyIntegration.choose_disjoint_card_identity
#print axioms BinaryFormMoat.EntropyIntegration.disjoint_subsetMean_eq
#print axioms BinaryFormMoat.EntropyIntegration.disjointLabelAverage
#print axioms BinaryFormMoat.EntropyIntegration.disjointLabelAverage_mono
#print axioms BinaryFormMoat.EntropyIntegration.disjointLabelAverage_ignore_prefix
#print axioms BinaryFormMoat.EntropyIntegration.disjointLabelAverage_const
#print axioms BinaryFormMoat.EntropyIntegration.disjointLabelAverage_sub
