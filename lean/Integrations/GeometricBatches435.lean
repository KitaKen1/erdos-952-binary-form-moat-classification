import Integrations.PaperPrimeInventory435

noncomputable section
open scoped Classical BigOperators
namespace BinaryFormMoat.GeometryIntegration

/-- The exact finite predecessor sum; no infinite series or asymptotic
summation oracle is required. -/
theorem geometric_predecessor_sum_mul (B : ℝ) (j : ℕ) :
    (B - 1) * (∑ i ∈ Finset.range j, B ^ i) = B ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- Any subsequence of the same progression has the paper's C*T/(B-1)
smaller-alphabet budget, including arbitrary gaps between used windows. -/
theorem geometric_smaller_weight_sum (B C : ℝ) (hB : 1 < B) (hC : 0 ≤ C)
    (I : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ i ∈ I, w i ≤ C * B ^ i) (j : ℕ) :
    ∑ i ∈ I.filter (fun i => i < j), w i ≤ C * B ^ j / (B - 1) := by
  have hsub : I.filter (fun i => i < j) ⊆ Finset.range j := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hsum : ∑ i ∈ I.filter (fun i => i < j), w i ≤
      C * ∑ i ∈ Finset.range j, B ^ i := by
    calc
      _ ≤ ∑ i ∈ I.filter (fun i => i < j), C * B ^ i :=
        Finset.sum_le_sum fun i hi => hw i (Finset.mem_filter.mp hi).1
      _ ≤ ∑ i ∈ Finset.range j, C * B ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hg := geometric_predecessor_sum_mul B j
  apply hsum.trans
  apply (le_div_iff₀ (by linarith : 0 < B - 1)).mpr
  nlinarith

/-- A fixed integer spacing is chosen before the growing finite family. -/
theorem exists_geometric_spacing (C δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 3 ≤ B ∧ C / ((B : ℝ) - 1) ≤ δ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max 2 (C / δ + 1))
  have hB2 : (2 : ℝ) < B := (le_max_left _ _).trans_lt hB
  have hratio : C / δ + 1 < (B : ℝ) := (le_max_right _ _).trans_lt hB
  refine ⟨B, by exact_mod_cast hB2, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < (B : ℝ) - 1)).mpr
  have h := (div_lt_iff₀ hδ).mp (by linarith : C / δ < (B : ℝ) - 1)
  linarith

theorem geometric_smaller_weight_sum_small (B : ℕ) (hB : 3 ≤ B)
    (C δ : ℝ) (hC : 0 ≤ C) (hbudget : C / ((B : ℝ) - 1) ≤ δ)
    (I : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ i ∈ I, w i ≤ C * (B ^ i : ℕ)) (j : ℕ) :
    ∑ i ∈ I.filter (fun i => i < j), w i ≤ δ * (B ^ j : ℕ) := by
  have h := geometric_smaller_weight_sum (B : ℝ) C (by exact_mod_cast (by omega : 1 < B))
    hC I w (by simpa only [Nat.cast_pow] using hw) j
  have hp : (0 : ℝ) ≤ (B : ℝ) ^ j := by positivity
  have hc := mul_le_mul_of_nonneg_right hbudget hp
  rw [div_mul_eq_mul_div] at hc
  simpa only [Nat.cast_pow] using h.trans hc

/-- Closed dyadic prime intervals are strictly separated when B>=3. -/
theorem geometric_dyadic_separated (B : ℕ) (hB : 3 ≤ B) (i j : ℕ) (hij : i < j) :
    2 * B ^ i < B ^ j := by
  have hp : 0 < B ^ i := pow_pos (by omega) _
  have hpow : B ^ (i + 1) ≤ B ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : 2 * B ^ i < B ^ (i + 1) := by
    rw [pow_succ]
    nlinarith
  exact hlt.trans_le hpow

theorem geometric_prime_batches_pairwise (B : ℕ) (hB : 3 ≤ B)
    (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, B ^ i ≤ p ∧ p ≤ 2 * B ^ i) :
    Set.Pairwise (I : Set ℕ) (fun i j => Disjoint (P i) (P j)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have h1 := hP i hi p hpi
  have h2 := hP j hj p hpj
  rcases lt_or_gt_of_ne hij with h | h
  · have := geometric_dyadic_separated B hB i j h
    omega
  · have := geometric_dyadic_separated B hB j i h
    omega

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.geometric_predecessor_sum_mul
#print axioms BinaryFormMoat.GeometryIntegration.geometric_smaller_weight_sum
#print axioms BinaryFormMoat.GeometryIntegration.exists_geometric_spacing
#print axioms BinaryFormMoat.GeometryIntegration.geometric_smaller_weight_sum_small
#print axioms BinaryFormMoat.GeometryIntegration.geometric_dyadic_separated
#print axioms BinaryFormMoat.GeometryIntegration.geometric_prime_batches_pairwise
