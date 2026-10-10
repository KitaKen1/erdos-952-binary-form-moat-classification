import Integrations.SubsetProjection435
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration

/-- Uniform auxiliary mean; it remains OUTSIDE the entropy experiment. -/
def finiteUniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem finiteUniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ a, f a ≤ g a) : finiteUniformMean f ≤ finiteUniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem finiteUniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    finiteUniformMean (fun _ : α => c) = c := by
  simp [finiteUniformMean, Fintype.card_ne_zero]

theorem finiteUniformMean_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    finiteUniformMean (fun a => ∑ i, f i a) = ∑ i, finiteUniformMean (f i) := by
  simp only [finiteUniformMean, Finset.sum_div]
  exact Finset.sum_comm

/-- Swap one current coordinate with a new draw. This is an involution
on the ACTUAL dependent finite auxiliary product and needs no independence
assumption about any walk-residue law. -/
def productCoordinateSwap {ι : Type*} [DecidableEq ι] (A : ι → Type*) (i : ι) :
    (((j : ι) → A j) × A i) ≃ (((j : ι) → A j) × A i) := by
  let g : (((j : ι) → A j) × A i) → (((j : ι) → A j) × A i) :=
    fun v => (Function.update v.1 i v.2, v.1 i)
  have hg : Function.Involutive g := by
    intro v
    dsimp only [g]
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp
  exact ⟨g, g, hg, hg⟩

/-- Averaging a coordinate refresh preserves the exact global product mean. -/
theorem finiteUniformMean_coordinate_refresh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : ι) (f : ((j : ι) → A j) → ℝ) :
    finiteUniformMean (fun a => finiteUniformMean (fun q : A i => f (Function.update a i q))) =
      finiteUniformMean f := by
  have hs : (∑ a : (j : ι) → A j, ∑ q : A i, f (Function.update a i q)) =
      (∑ a : (j : ι) → A j, ∑ _q : A i, f a) := by
    calc
      _ = ∑ v : ((j : ι) → A j) × A i, f (Function.update v.1 i v.2) :=
        (Fintype.sum_prod_type _).symm
      _ = ∑ v : ((j : ι) → A j) × A i, f v.1 :=
        Fintype.sum_equiv (productCoordinateSwap A i) _ _ (fun _ => rfl)
      _ = _ := Fintype.sum_prod_type _
  dsimp only [finiteUniformMean]
  rw [← Finset.sum_div, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero (α := A i))]

/-- Every single-coordinate conditional auxiliary lower mean gives the
global lower mean. The averaging does not enlarge the conditioned prior. -/
theorem finiteUniformMean_ge_of_coordinate_refresh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (i : ι) (f : ((j : ι) → A j) → ℝ) (c : ℝ)
    (h : ∀ a, c ≤ finiteUniformMean (fun q : A i => f (Function.update a i q))) :
    c ≤ finiteUniformMean f := by
  have hm := finiteUniformMean_mono (fun _ => c)
    (fun a => finiteUniformMean (fun q : A i => f (Function.update a i q))) h
  rw [finiteUniformMean_const, finiteUniformMean_coordinate_refresh] at hm
  exact hm

/-- Sum ALL batch lower means under ONE actual product of choices. -/
theorem finiteUniformMean_product_sum_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (f : ι → ((j : ι) → A j) → ℝ) (c : ι → ℝ)
    (h : ∀ i a, c i ≤ finiteUniformMean (fun q : A i => f i (Function.update a i q))) :
    (∑ i, c i) ≤ finiteUniformMean (fun a => ∑ i, f i a) := by
  rw [finiteUniformMean_sum]
  exact Finset.sum_le_sum (fun i _ => finiteUniformMean_ge_of_coordinate_refresh A i (f i) (c i) (h i))

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_mono
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_const
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_sum
#print axioms BinaryFormMoat.EntropyIntegration.productCoordinateSwap
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_coordinate_refresh
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_ge_of_coordinate_refresh
#print axioms BinaryFormMoat.EntropyIntegration.finiteUniformMean_product_sum_lower
