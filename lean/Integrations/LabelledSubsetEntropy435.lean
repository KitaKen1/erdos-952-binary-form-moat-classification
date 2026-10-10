import Integrations.SubsetEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem subsetLabelAverage_add {ι R : Type*} [Fintype ι] [Fintype R]
    (s : ℕ) (f g : Finset ι → (ι → R) → ℝ) :
    subsetLabelAverage s (fun A ρ => f A ρ + g A ρ) =
      subsetLabelAverage s f + subsetLabelAverage s g := by
  classical
  simp only [subsetLabelAverage, Finset.sum_add_distrib, add_div]

theorem subsetLabelAverage_div {ι R : Type*} [Fintype ι] [Fintype R]
    (s : ℕ) (f : Finset ι → (ι → R) → ℝ) (c : ℝ) :
    subsetLabelAverage s (fun A ρ => f A ρ / c) = subsetLabelAverage s f / c := by
  classical
  simp only [subsetLabelAverage, ← Finset.sum_div]
  ring

/-- A subset-independent quantity keeps its label average. -/
theorem subsetLabelAverage_ignore_subset {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (s : ℕ) (hs : s ≤ Fintype.card ι) (g : (ι → R) → ℝ) :
    subsetLabelAverage s (fun _ ρ => g ρ) = (∑ ρ, g ρ) / Fintype.card (ι → R) := by
  classical
  have hc : ((((Finset.univ : Finset ι).powersetCard s).card : ℕ) : ℝ) ≠ 0 := by
    simp only [Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast (Nat.choose_pos hs).ne'
  simp only [subsetLabelAverage, Finset.sum_const, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hc]
  congr 3 <;> exact Subsingleton.elim _ _

/-- Global independent labels can be averaged before or after the fixed-size subset. -/
theorem subsetLabelAverage_eq_mean_subsetMean {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (s : ℕ) (f : Finset ι → (ι → R) → ℝ) :
    subsetLabelAverage s f =
      (∑ ρ : ι → R, subsetMean s (fun A => f A ρ)) / Fintype.card (ι → R) := by
  classical
  simp only [subsetLabelAverage, subsetMean, Finset.sum_div, div_div]
  rw [Finset.sum_comm]
  simp only [mul_comm]
  congr 1 <;> first | rfl | (ext; simp)

/-- Han's inequality averaged over independent root labels. -/
theorem subsetLabelAverage_forward_increment_le {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (s : ℕ) (hs : 0 < s) (hsk : s < Fintype.card ι)
    (f : Finset ι → (ι → R) → ℝ) (hf : ∀ ρ, f ∅ ρ = 0)
    (h : ∀ ρ, ∀ A B : Finset ι, A ⊆ B → ∀ j, j ∉ B →
      f (insert j B) ρ - f B ρ ≤ f (insert j A) ρ - f A ρ) :
    subsetLabelAverage (s + 1) f - subsetLabelAverage s f ≤ subsetLabelAverage s f / s := by
  classical
  simp_rw [subsetLabelAverage_eq_mean_subsetMean]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ρ _ =>
    subsetMean_forward_increment_le s hs hsk (fun A => f A ρ) (hf ρ) (h ρ))
  have hd := div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ Fintype.card (ι → R) by positivity)
  simpa only [← Finset.sum_div, div_div, mul_comm] using hd

section Coordinates
variable {Ω ι R : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype R]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
  [∀ i, MeasurableSingletonClass (K i)]
  (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
  (X : ∀ i, R → Ω → K i) (hX : ∀ i r, Measurable (X i r))

include hX in
/-- Mean entropy of a fresh unused index, with its independently uniform label. -/
theorem labelledSubsetEntropy_average_fresh (s : ℕ) (hs : s < Fintype.card ι) :
    subsetLabelAverage s (fun A ρ =>
      (∑ j ∈ Finset.univ \ A,
        condEntropy (X j (ρ j)) (subsetObservation K (fun i => X i (ρ i)) A) μ) /
          (Fintype.card ι - s : ℕ)) =
      subsetLabelAverage (s + 1) (fun A ρ => subsetEntropy K μ (fun i => X i (ρ i)) A) -
        subsetLabelAverage s (fun A ρ => subsetEntropy K μ (fun i => X i (ρ i)) A) := by
  classical
  simp_rw [subsetLabelAverage_eq_mean_subsetMean]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  have h := subsetEntropy_average_fresh K μ (fun i => X i (ρ i)) (fun i => hX i (ρ i)) s hs
  simpa only [subsetMean, ← Finset.sum_div, div_div, Nat.cast_mul, mul_comm] using h

include hX in
/-- This replaces the concavity step in the paper without changing the sampling law. -/
theorem labelledSubsetEntropy_forward_increment_le (s : ℕ) (hs : 0 < s)
    (hsk : s < Fintype.card ι) :
    subsetLabelAverage (s + 1) (fun A ρ => subsetEntropy K μ (fun i => X i (ρ i)) A) -
      subsetLabelAverage s (fun A ρ => subsetEntropy K μ (fun i => X i (ρ i)) A) ≤
        subsetLabelAverage s (fun A ρ => subsetEntropy K μ (fun i => X i (ρ i)) A) / s := by
  apply subsetLabelAverage_forward_increment_le s hs hsk
  · intro ρ
    exact subsetEntropy_empty K μ _
  · intro ρ
    exact subsetEntropy_diminishing_returns K μ _ (fun i => hX i (ρ i))

end Coordinates
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_add
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_div
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_eq_mean_subsetMean
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_forward_increment_le
#print axioms BinaryFormMoat.EntropyIntegration.labelledSubsetEntropy_average_fresh
#print axioms BinaryFormMoat.EntropyIntegration.labelledSubsetEntropy_forward_increment_le

#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_ignore_subset
