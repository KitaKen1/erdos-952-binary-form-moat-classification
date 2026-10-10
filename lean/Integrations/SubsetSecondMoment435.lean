import Integrations.SubsetSampling435

noncomputable section

namespace BinaryFormMoat.EntropyIntegration

/-- The off-diagonal inclusion count is constant for sampling distinct indices. -/
theorem powersetCard_pair_mem_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (i j : ι) (hij : i ≠ j) :
    (((Finset.univ : Finset ι).powersetCard s).filter
      (fun A => i ∈ A ∧ j ∈ A)).card =
        Nat.choose (Fintype.card ι - 2) (s - 2) := by
  have hc : ({i, j} : Finset ι).card = 2 := by simp [hij]
  simpa [hc, Finset.insert_subset_iff, Finset.singleton_subset_iff] using
    Finset.card_filter_powersetCard_subset ({i, j} : Finset ι)
    Finset.univ s (by simp) (by rw [hc]; exact hs)

/-- Expand the square before averaging; no independence is assumed. -/
theorem sum_subset_sq_by_pair_fibers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (Finset ι)) (w : ι → ℝ) :
    (∑ A ∈ C, (∑ i ∈ A, w i) ^ 2) =
      ∑ i, ∑ j, ((C.filter (fun A => i ∈ A ∧ j ∈ A)).card : ℝ) * w i * w j := by
  have he : ∀ A : Finset ι, (∑ i ∈ A, w i) = ∑ i, if i ∈ A then w i else 0 := by
    intro A
    rw [← Finset.sum_filter]
    simp
  simp_rw [he, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hp : ∀ A : Finset ι,
      (if i ∈ A then w i else 0) * (if j ∈ A then w j else 0) =
        if i ∈ A ∧ j ∈ A then w i * w j else 0 := by
    intro A
    split_ifs <;> simp_all
  simp_rw [hp]
  rw [← Finset.sum_filter]
  simp [mul_assoc]

/-- Centering makes all off-diagonal contributions nonpositive in aggregate. -/
theorem powersetCard_centered_second_moment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ Fintype.card ι) (w : ι → ℝ)
    (hzero : ∑ i, w i = 0) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s, (∑ i ∈ A, w i) ^ 2) /
      ((Finset.univ : Finset ι).powersetCard s).card ≤
        ((s : ℝ) / Fintype.card ι) * ∑ i, (w i) ^ 2 := by
  let C := (Finset.univ : Finset ι).powersetCard s
  let c₁ : ℝ := Nat.choose (Fintype.card ι - 1) (s - 1)
  let c₂ : ℝ := Nat.choose (Fintype.card ι - 2) (s - 2)
  have hdiag (i : ι) : ((C.filter (fun A => i ∈ A)).card : ℝ) = c₁ := by
    simp only [C, c₁]
    congr 1
    simpa using Finset.card_filter_powersetCard_subset ({i} : Finset ι)
      Finset.univ s (by simp) (by simpa using (by omega : 1 ≤ s))
  have hcount (i j : ι) : ((C.filter (fun A => i ∈ A ∧ j ∈ A)).card : ℝ) =
      if i = j then c₁ else c₂ := by
    by_cases hij : i = j
    · subst j
      simpa using hdiag i
    · simp only [hij, ↓reduceIte]
      simpa only [C, c₂] using congrArg (fun n : ℕ => (n : ℝ))
        (powersetCard_pair_mem_card s hs i j hij)
  have hinner (i : ι) :
      (∑ j, ((C.filter (fun A => i ∈ A ∧ j ∈ A)).card : ℝ) * w i * w j) =
        (c₁ - c₂) * (w i) ^ 2 := by
    calc
      _ = ∑ j, (c₂ * w i * w j + if j = i then (c₁ - c₂) * (w i) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcount]
        by_cases hij : i = j
        · subst j
          simp only [↓reduceIte]
          ring
        · simp only [hij, Ne.symm hij, ↓reduceIte]
          ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero]; simp
  have he : (∑ A ∈ C, (∑ i ∈ A, w i) ^ 2) = (c₁ - c₂) * ∑ i, (w i) ^ 2 := by
    rw [sum_subset_sq_by_pair_fibers]
    simp_rw [hinner]
    rw [Finset.mul_sum]
  have hc : (0 : ℝ) < C.card := by
    exact_mod_cast ((Finset.powersetCard_nonempty.mpr (by simpa using hsk)).card_pos)
  have hn : 0 ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc₂ : 0 ≤ c₂ := Nat.cast_nonneg _
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hratio : c₁ / C.card = (s : ℝ) / Fintype.card ι := by
    rw [← hdiag i]
    exact powersetCard_mem_fraction s (by omega) hsk i
  change (∑ A ∈ C, (∑ i ∈ A, w i) ^ 2) / C.card ≤ _
  calc
    _ = ((c₁ - c₂) * ∑ i, (w i) ^ 2) / C.card := by rw [he]
    _ ≤ (c₁ * ∑ i, (w i) ^ 2) / C.card := by
      apply div_le_div_of_nonneg_right _ hc.le
      nlinarith only [mul_nonneg hc₂ hn]
    _ = (c₁ / C.card) * ∑ i, (w i) ^ 2 := by ring
    _ = _ := by rw [hratio]

/-- The variance of the subset sum is at most s times the squared centered range. -/
theorem powersetCard_centered_second_moment_range {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ Fintype.card ι) (w : ι → ℝ)
    (hzero : ∑ i, w i = 0) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, |w i| ≤ W) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s, (∑ i ∈ A, w i) ^ 2) /
      ((Finset.univ : Finset ι).powersetCard s).card ≤ (s : ℝ) * W ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hb : (∑ i, (w i) ^ 2) ≤ (Fintype.card ι : ℝ) * W ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, W ^ 2 := Finset.sum_le_sum (fun i _ => by
        have h := (sq_le_sq₀ (abs_nonneg (w i)) hW).mpr (hw i)
        simpa only [sq_abs] using h)
      _ = _ := by simp
  calc
    _ ≤ ((s : ℝ) / Fintype.card ι) * ∑ i, (w i) ^ 2 :=
      powersetCard_centered_second_moment_le s hs hsk w hzero
    _ ≤ ((s : ℝ) / Fintype.card ι) * ((Fintype.card ι : ℝ) * W ^ 2) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg (Nat.cast_nonneg _) hn.le)
    _ = _ := by field_simp

/-- Chebyshev as an exact uniform-subset cardinal fraction. -/
theorem powersetCard_centered_tail_fraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ Fintype.card ι) (w : ι → ℝ)
    (hzero : ∑ i, w i = 0) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, |w i| ≤ W)
    (a : ℝ) (ha : 0 < a) :
    ((((Finset.univ : Finset ι).powersetCard s).filter
      (fun A => a ≤ |∑ i ∈ A, w i|)).card : ℝ) /
      ((Finset.univ : Finset ι).powersetCard s).card ≤ (s : ℝ) * W ^ 2 / a ^ 2 := by
  let C := (Finset.univ : Finset ι).powersetCard s
  let B := C.filter (fun A => a ≤ |∑ i ∈ A, w i|)
  have hc : (0 : ℝ) < C.card := by
    exact_mod_cast ((Finset.powersetCard_nonempty.mpr (by simpa using hsk)).card_pos)
  have hb : (B.card : ℝ) * a ^ 2 ≤ ∑ A ∈ C, (∑ i ∈ A, w i) ^ 2 := by
    calc
      _ = ∑ _A ∈ B, a ^ 2 := by simp
      _ ≤ ∑ A ∈ B, (∑ i ∈ A, w i) ^ 2 := by
        apply Finset.sum_le_sum
        intro A hA
        have h := (Finset.mem_filter.mp hA).2
        have hsquare := (sq_le_sq₀ ha.le (abs_nonneg (∑ i ∈ A, w i))).mpr h
        simpa only [sq_abs] using hsquare
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
  have hmoment := powersetCard_centered_second_moment_range s hs hsk w hzero W hW hw
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  change (B.card : ℝ) / C.card * a ^ 2 ≤ _
  calc
    _ = ((B.card : ℝ) * a ^ 2) / C.card := by ring
    _ ≤ (∑ A ∈ C, (∑ i ∈ A, w i) ^ 2) / C.card :=
      div_le_div_of_nonneg_right hb hc.le
    _ ≤ _ := hmoment

/-- The population mean remains in the same closed interval. -/
theorem finite_real_mean_bounds {ι : Type*} [Fintype ι]
    (hk : 0 < Fintype.card ι) (w : ι → ℝ) (lo hi : ℝ)
    (hw : ∀ i, lo ≤ w i ∧ w i ≤ hi) :
    lo ≤ (∑ i, w i) / Fintype.card ι ∧
      (∑ i, w i) / Fintype.card ι ≤ hi := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk
  constructor
  · apply (le_div_iff₀ hn).mpr
    calc
      _ = ∑ _i : ι, lo := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (hw i).1)
  · apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ _i : ι, hi := Finset.sum_le_sum (fun i _ => (hw i).2)
      _ = _ := by simp [mul_comm]

/-- A lower-tail bound for a uniform subset, centered at its exact population mean. -/
theorem powersetCard_interval_lower_tail_fraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ Fintype.card ι)
    (w : ι → ℝ) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (hw : ∀ i, lo ≤ w i ∧ w i ≤ hi) (a : ℝ) (ha : 0 < a) :
    ((((Finset.univ : Finset ι).powersetCard s).filter
      (fun A => (∑ i ∈ A, w i) ≤ (s : ℝ) *
        ((∑ i, w i) / Fintype.card ι) - a)).card : ℝ) /
      ((Finset.univ : Finset ι).powersetCard s).card ≤ (s : ℝ) * (hi - lo) ^ 2 / a ^ 2 := by
  let m := (∑ i, w i) / Fintype.card ι
  let v : ι → ℝ := fun i => w i - m
  have hk : 0 < Fintype.card ι := by omega
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  obtain ⟨hml, hmh⟩ := finite_real_mean_bounds hk w lo hi hw
  have hv : ∀ i, |v i| ≤ hi - lo := by
    intro i
    rw [abs_le]
    obtain ⟨hli, hhi⟩ := hw i
    dsimp [v, m]
    constructor <;> linarith
  have hzero : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [m]
    field_simp
    ring
  have ht := powersetCard_centered_tail_fraction s hs hsk v hzero (hi - lo)
    (sub_nonneg.mpr hlohi) hv a ha
  apply le_trans _ ht
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro A hA
  obtain ⟨hC, hsum⟩ := Finset.mem_filter.mp hA
  change (∑ i ∈ A, w i) ≤ (s : ℝ) * m - a at hsum
  apply Finset.mem_filter.mpr
  refine ⟨hC, ?_⟩
  have hcard : A.card = s := (Finset.mem_powersetCard.mp hC).2
  have he : (∑ i ∈ A, v i) = (∑ i ∈ A, w i) - (s : ℝ) * m := by
    simp [v, Finset.sum_sub_distrib, hcard]
  have hl : a ≤ -(∑ i ∈ A, v i) := by rw [he]; linarith only [hsum]
  exact hl.trans (neg_le_abs _)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_pair_mem_card
#print axioms BinaryFormMoat.EntropyIntegration.sum_subset_sq_by_pair_fibers
#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_centered_second_moment_le
#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_centered_second_moment_range
#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_centered_tail_fraction

#print axioms BinaryFormMoat.EntropyIntegration.finite_real_mean_bounds
#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_interval_lower_tail_fraction
