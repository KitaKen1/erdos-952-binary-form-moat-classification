import Integrations.FiniteEntropy435
import Integrations.CoordinateEntropy435
import Mathlib.Data.Finset.Powerset

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Exact inclusion probability for a uniformly chosen subset without replacement. -/
theorem powersetCard_mem_fraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (i : ι) :
    ((((Finset.univ : Finset ι).powersetCard s).filter (fun A => i ∈ A)).card : ℝ) /
      ((Finset.univ : Finset ι).powersetCard s).card = (s : ℝ) / Fintype.card ι := by
  have hc : (((Finset.univ : Finset ι).powersetCard s).filter (fun A => i ∈ A)).card =
      Nat.choose (Fintype.card ι - 1) (s - 1) := by
    simpa using Finset.card_filter_powersetCard_subset ({i} : Finset ι) Finset.univ s
      (by simp) (by simpa using hs)
  have hk : 1 ≤ Fintype.card ι := hs.trans hsk
  have hm := Nat.add_one_mul_choose_eq (Fintype.card ι - 1) (s - 1)
  rw [Nat.sub_add_cancel hk, Nat.sub_add_cancel hs] at hm
  rw [hc, Finset.card_powersetCard, Finset.card_univ]
  apply (div_eq_div_iff (by exact_mod_cast (Nat.choose_pos hsk).ne')
    (by exact_mod_cast (by omega : Fintype.card ι ≠ 0))).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hm)

theorem sum_subset_weight_by_fibers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (Finset ι)) (w : ι → ℝ) :
    (∑ A ∈ C, ∑ i ∈ A, w i) = ∑ i, ((C.filter (fun A => i ∈ A)).card : ℝ) * w i := by
  classical
  have hsum : ∀ A : Finset ι, (∑ i ∈ A, w i) = ∑ i, if i ∈ A then w i else 0 := by
    intro A
    rw [← Finset.sum_filter]
    simp
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp

theorem powersetCard_average_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (w : ι → ℝ) :
    (∑ A ∈ (Finset.univ : Finset ι).powersetCard s, ∑ i ∈ A, w i) /
      ((Finset.univ : Finset ι).powersetCard s).card =
        ((s : ℝ) / Fintype.card ι) * ∑ i, w i := by
  rw [sum_subset_weight_by_fibers, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (((((Finset.univ : Finset ι).powersetCard s).filter (fun A => i ∈ A)).card : ℝ) /
        ((Finset.univ : Finset ι).powersetCard s).card) * w i := by ring
    _ = _ := by rw [powersetCard_mem_fraction s hs hsk i]

/-- Choosing every label in advance has the correct uniform marginal, even
when only the selected subset of labels will be used. -/
theorem label_assignment_average_eval {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (i : ι) (w : R → ℝ) :
    (∑ ρ : ι → R, w (ρ i)) / (Fintype.card (ι → R) : ℝ) =
      (∑ r : R, w r) / (Fintype.card R : ℝ) := by
  classical
  let S : ι → Finset R := fun _ => Finset.univ
  have hbox : Fintype.piFinset S = (Finset.univ : Finset (ι → R)) := by ext; simp [S]
  have hmap : (uniformOn ((Finset.univ : Finset (ι → R)) : Set (ι → R))).map (fun ρ => ρ i) =
      uniformOn ((Finset.univ : Finset R) : Set R) := by
    have h := uniformOn_box_coordinate_map S (fun _ => by simp [S]) i
    simpa only [hbox, S] using h
  calc
    _ = ∫ ρ, w (ρ i) ∂uniformOn ((Finset.univ : Finset (ι → R)) : Set (ι → R)) :=
      (integral_uniformOn_finset Finset.univ _).symm
    _ = ∫ r, w r ∂uniformOn ((Finset.univ : Finset R) : Set R) := by
      rw [← hmap]
      exact (integral_map (measurable_pi_apply i).aemeasurable
        (measurable_of_finite w).aestronglyMeasurable).symm
    _ = _ := integral_uniformOn_finset Finset.univ w

noncomputable def subsetLabelAverage {ι R : Type*} [Fintype ι] [Fintype R]
    (s : ℕ) (f : Finset ι → (ι → R) → ℝ) : ℝ := by
  classical
  exact (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
    (∑ ρ : ι → R, f A ρ) / (Fintype.card (ι → R) : ℝ)) /
      ((Finset.univ : Finset ι).powersetCard s).card

/-- Linear expectations over distinct indices and independent uniform labels.
The auxiliary choice is averaged outside the entropy experiment. -/
theorem subsetLabelAverage_sum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (w : ι → R → ℝ) :
    subsetLabelAverage s (fun A ρ => ∑ i ∈ A, w i (ρ i)) =
      ((s : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ))) * ∑ i, ∑ r, w i r := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  unfold subsetLabelAverage
  have hinner : ∀ A : Finset ι,
      (∑ ρ : ι → R, ∑ i ∈ A, w i (ρ i)) / (Fintype.card (ι → R) : ℝ) =
        ∑ i ∈ A, (∑ r, w i r) / (Fintype.card R : ℝ) := by
    intro A
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    exact label_assignment_average_eval i (w i)
  calc
    _ = (∑ A ∈ (Finset.univ : Finset ι).powersetCard s,
        ∑ i ∈ A, (∑ r, w i r) / (Fintype.card R : ℝ)) /
          ((Finset.univ : Finset ι).powersetCard s).card := by
      congr 1
      exact Finset.sum_congr rfl (fun A _ => hinner A)
    _ = ((s : ℝ) / Fintype.card ι) *
        ∑ i, (∑ r, w i r) / (Fintype.card R : ℝ) :=
      powersetCard_average_sum s hs hsk _
    _ = _ := by rw [← Finset.sum_div]; ring

theorem subsetLabelAverage_mono {ι R : Type*} [Fintype ι] [Fintype R]
    (s : ℕ) (f g : Finset ι → (ι → R) → ℝ)
    (h : ∀ A ∈ (Finset.univ : Finset ι).powersetCard s, ∀ ρ, f A ρ ≤ g A ρ) :
    subsetLabelAverage s f ≤ subsetLabelAverage s g := by
  classical
  unfold subsetLabelAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro A hA
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun ρ _ => h A hA ρ)

theorem subsetLabelAverage_const {ι R : Type*} [Fintype ι] [Fintype R] [Nonempty R]
    (s : ℕ) (hsk : s ≤ Fintype.card ι) (c : ℝ) :
    subsetLabelAverage (ι := ι) (R := R) s (fun _ _ => c) = c := by
  classical
  have hC : (((Finset.univ : Finset ι).powersetCard s).card : ℝ) ≠ 0 := by
    exact_mod_cast ((Finset.powersetCard_nonempty.mpr (by simpa using hsk)).card_ne_zero)
  have hQ : (Fintype.card (ι → R) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold subsetLabelAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ c hQ]
  exact mul_div_cancel_left₀ c hC

theorem subsetLabelAverage_sub {ι R : Type*} [Fintype ι] [Fintype R]
    (s : ℕ) (f g : Finset ι → (ι → R) → ℝ) :
    subsetLabelAverage s (fun A ρ => f A ρ - g A ρ) =
      subsetLabelAverage s f - subsetLabelAverage s g := by
  classical
  simp [subsetLabelAverage, Finset.sum_sub_distrib, sub_div]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_mem_fraction
#print axioms BinaryFormMoat.EntropyIntegration.sum_subset_weight_by_fibers
#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_average_sum
#print axioms BinaryFormMoat.EntropyIntegration.label_assignment_average_eval
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_sum
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_mono
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_const
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_sub
