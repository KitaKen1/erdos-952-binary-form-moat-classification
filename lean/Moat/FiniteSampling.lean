import Moat.RootSampling
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace BinaryFormMoat

section FiniteBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ι → Type*}

/-- A rectangular event in a finite product has exactly the product of its
coordinate counts. This is the finite counting form of independence. -/
theorem box_event_count (S : ∀ i, Finset (K i)) (Q : ∀ i, K i → Prop)
    [∀ i, DecidablePred (Q i)] :
    ((Fintype.piFinset S).filter (fun σ => ∀ i, Q i (σ i))).card =
      ∏ i, ((S i).filter (Q i)).card := by
  have he : (Fintype.piFinset S).filter (fun σ => ∀ i, Q i (σ i)) =
      Fintype.piFinset (fun i => (S i).filter (Q i)) := by
    ext σ
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    exact forall_and.symm
  rw [he, Fintype.card_piFinset]

/-- Exact factorization of uniform event fractions. If every S_i is nonempty,
these are probabilities for the single uniform law on the entire product.
The algebraic identity also holds with the zero-denominator convention. -/
theorem box_event_fraction (S : ∀ i, Finset (K i)) (Q : ∀ i, K i → Prop)
    [∀ i, DecidablePred (Q i)] :
    (((Fintype.piFinset S).filter (fun σ => ∀ i, Q i (σ i))).card : ℝ) /
      (Fintype.piFinset S).card =
        ∏ i, (((S i).filter (Q i)).card : ℝ) / (S i).card := by
  rw [box_event_count, Fintype.card_piFinset]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

/-- Marginal event counts in a finite product. -/
theorem box_cylinder_count (S : ∀ i, Finset (K i)) (i : ι)
    (Q : K i → Prop) [DecidablePred Q] :
    ((Fintype.piFinset S).filter (fun σ => Q (σ i))).card =
      ((S i).filter Q).card * ∏ j ∈ Finset.univ.erase i, (S j).card := by
  classical
  have he : (Fintype.piFinset S).filter (fun σ => Q (σ i)) =
      Fintype.piFinset (Function.update S i ((S i).filter Q)) := by
    rw [Fintype.piFinset_update_eq_filter_piFinset_mem S i (Finset.filter_subset Q (S i))]
    ext σ
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hS, hQ⟩
      exact ⟨hS, hS i, hQ⟩
    · rintro ⟨hS, _, hQ⟩
      exact ⟨hS, hQ⟩
  rw [he, Fintype.card_piFinset]
  have hu : (fun j => (Function.update S i ((S i).filter Q) j).card) =
      Function.update (fun j => (S j).card) i ((S i).filter Q).card := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  rw [hu, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]

/-- A marginal under the common uniform product law is the expected uniform
law on its coordinate; nonempty factors are checked explicitly. -/
theorem box_cylinder_fraction (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty)
    (i : ι) (Q : K i → Prop) [DecidablePred Q] :
    (((Fintype.piFinset S).filter (fun σ => Q (σ i))).card : ℝ) /
      (Fintype.piFinset S).card = ((S i).filter Q).card / ((S i).card : ℝ) := by
  rw [box_cylinder_count, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ (fun j => (S j).card) (Finset.mem_univ i)]
  push_cast
  have hprod : (∏ j ∈ Finset.univ.erase i, ((S j).card : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (hS j).card_ne_zero
  exact mul_div_mul_right _ _ hprod

/-- The weighted sum of coordinate hits, averaged over one common product law,
is the sum of the marginal hit rates. No measure-theoretic adapter is needed. -/
theorem box_average_weighted_hits (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty)
    (Q : ∀ i, K i → Prop) [∀ i, DecidablePred (Q i)] (w : ι → ℝ) :
    (∑ σ ∈ Fintype.piFinset S, ∑ i, if Q i (σ i) then w i else 0) /
      (Fintype.piFinset S).card =
        ∑ i, w i * (((S i).filter (Q i)).card / ((S i).card : ℝ)) := by
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm, mul_div_assoc, box_cylinder_fraction S hS i (Q i)]

end FiniteBoxes

/-- Simultaneous hits of independent, uniformly selected slopes have at most
the product of the reciprocal alphabet sizes as their probability. -/
theorem joint_slope_hit_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] [∀ i, DecidableEq (K i)]
    (S : ∀ i, Finset (K i)) (a b : ∀ i, K i)
    (hab : ∀ i, a i ≠ 0 ∨ b i ≠ 0) :
    (((Fintype.piFinset S).filter (fun σ => ∀ i, a i = σ i * b i)).card : ℝ) /
      (Fintype.piFinset S).card ≤ ∏ i, 1 / ((S i).card : ℝ) := by
  rw [box_event_fraction S (fun i x => a i = x * b i)]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    exact uniform_slope_hit_bound (S i) (a i) (b i) (hab i)

/-- Degree-weighted hit costs average to at most one per coordinate under a
single uniform product law. Weights may vary with the prime. -/
theorem average_weighted_slope_hits_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Field (K i)] [∀ i, DecidableEq (K i)]
    (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty) (a b : ∀ i, K i)
    (hab : ∀ i, a i ≠ 0 ∨ b i ≠ 0) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ σ ∈ Fintype.piFinset S, ∑ i,
      if a i = σ i * b i then (S i).card * w i else 0) /
        (Fintype.piFinset S).card ≤ ∑ i, w i := by
  rw [box_average_weighted_hits S hS (fun i x => a i = x * b i)
    (fun i => (S i).card * w i)]
  apply Finset.sum_le_sum
  intro i _
  have he := mul_le_mul_of_nonneg_right
    (weighted_uniform_slope_hit_bound (S i) (a i) (b i) (hab i)) (hw i)
  convert he using 1 <;> ring

end BinaryFormMoat
