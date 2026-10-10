import Integrations.DisjointSubset435
import Integrations.UniformDifferenceEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Finite mean lower bound paying only the fraction of failed choices. -/
theorem finite_mean_ge_good_fraction {J : Type*} [DecidableEq J]
    (C : Finset J) (hne : C.Nonempty) (bad : J → Prop) [DecidablePred bad]
    (E : J → ℝ) (L ε : ℝ) (hL : 0 ≤ L)
    (hbad : ((C.filter bad).card : ℝ) / C.card ≤ ε)
    (hE : ∀ j ∈ C, 0 ≤ E j) (hgood : ∀ j ∈ C, ¬ bad j → L ≤ E j) :
    (1 - ε) * L ≤ (∑ j ∈ C, E j) / C.card := by
  let good := C.filter (fun j => ¬ bad j)
  have hc : good.card + (C.filter bad).card = C.card := by
    simpa only [good, add_comm] using Finset.card_filter_add_card_filter_not (s := C) bad
  have hcr : (good.card : ℝ) + (C.filter bad).card = C.card := by exact_mod_cast hc
  have hs : (good.card : ℝ) * L ≤ ∑ j ∈ C, E j := by
    calc
      _ = ∑ _j ∈ good, L := by simp
      _ ≤ ∑ j ∈ good, E j := Finset.sum_le_sum (fun j hj =>
        hgood j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j hj _ => hE j hj)
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
  have hf : 1 - ε ≤ (good.card : ℝ) / C.card := by
    have he : (good.card : ℝ) / C.card + (C.filter bad).card / C.card = 1 := by
      rw [← add_div, hcr, div_self hC.ne']
    linarith
  calc
    _ ≤ ((good.card : ℝ) / C.card) * L := mul_le_mul_of_nonneg_right hf hL
    _ = ((good.card : ℝ) * L) / C.card := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hC.le

/-- Global labels include unused coordinates, preserving the independent root law. -/
def labelledSubsetChoices {ι R : Type*} [Fintype ι] [Fintype R]
    (r : ℕ) : Finset (Finset ι × (ι → R)) := by
  classical
  exact ((Finset.univ : Finset ι).powersetCard r) ×ˢ Finset.univ

theorem labelledSubsetChoices_nonempty {ι R : Type*} [Fintype ι] [Fintype R] [Nonempty R]
    (r : ℕ) (hr : r ≤ Fintype.card ι) : (labelledSubsetChoices (ι := ι) (R := R) r).Nonempty := by
  classical
  unfold labelledSubsetChoices
  obtain ⟨J, hJ⟩ := Finset.powersetCard_nonempty.mpr (show r ≤ (Finset.univ : Finset ι).card by simpa using hr)
  let ρ : ι → R := fun _ => Classical.choice (inferInstance : Nonempty R)
  exact ⟨(J, ρ), Finset.mem_product.mpr ⟨hJ, Finset.mem_univ ρ⟩⟩

theorem subsetLabelAverage_eq_choicesMean {ι R : Type*} [Fintype ι] [Fintype R]
    (r : ℕ) (f : Finset ι → (ι → R) → ℝ) :
    subsetLabelAverage r f =
      (∑ c ∈ labelledSubsetChoices r, f c.1 c.2) / (labelledSubsetChoices (ι := ι) (R := R) r).card := by
  classical
  simp only [subsetLabelAverage, labelledSubsetChoices, Finset.sum_product,
    Finset.card_product, Finset.card_univ, Nat.cast_mul, Finset.sum_div, div_div]
  simp only [mul_comm]

end BinaryFormMoat.EntropyIntegration

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Projection
variable {ι R : Type*} [Fintype ι] [Fintype R] (K : ι → Type*)
  [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point → K i)

def labelledSubsetProjection (J : Finset ι) (ρ : ι → R) : Point → ((i : J) → K i.val) :=
  fun p i => F i.val (ρ i.val) p

def badLabelledSubsetChoices (H : Finset Point) (r : ℕ) : Finset (Finset ι × (ι → R)) := by
  classical
  exact (labelledSubsetChoices r).filter
    (fun c => ¬ Set.InjOn (labelledSubsetProjection K F c.1 c.2) (H : Set Point))

def badLabelledSubsetFraction (H : Finset Point) (r : ℕ) : ℝ :=
  ((badLabelledSubsetChoices K F H r).card : ℝ) / (labelledSubsetChoices (ι := ι) (R := R) r).card

def labelledSubsetProjectionEntropyMean (H : Finset Point) (r : ℕ) : ℝ :=
  subsetLabelAverage r (fun J ρ => entropy (fun h : H => labelledSubsetProjection K F J ρ h.val)
    (uniformOn (Set.univ : Set H)))

omit [∀ i, Fintype (K i)] in
/-- Separate alphabets for different subsets need no masked-tuple encoding.
The entropy floor is derived from actual injection failures on distinct points. -/
theorem labelledSubsetProjectionEntropyMean_ge [Nonempty R]
    (H : Finset Point) (hne : H.Nonempty) (r : ℕ) (hr : r ≤ Fintype.card ι)
    (ε : ℝ) (herr : badLabelledSubsetFraction K F H r ≤ ε) :
    (1 - ε) * Real.log (H.card : ℝ) ≤ labelledSubsetProjectionEntropyMean K F H r := by
  classical
  rw [labelledSubsetProjectionEntropyMean, subsetLabelAverage_eq_choicesMean]
  apply finite_mean_ge_good_fraction (labelledSubsetChoices r) (labelledSubsetChoices_nonempty r hr)
    (fun c => ¬ Set.InjOn (labelledSubsetProjection K F c.1 c.2) (H : Set Point))
    (fun c => entropy (fun h : H => labelledSubsetProjection K F c.1 c.2 h.val)
      (uniformOn (Set.univ : Set H))) _ ε
  · exact Real.log_nonneg (by exact_mod_cast hne.card_pos)
  · exact herr
  · intro c _
    exact entropy_nonneg _ _
  · intro c _ hc
    push Not at hc
    exact (uniform_subtype_projection_entropy H hne (labelledSubsetProjection K F c.1 c.2) hc).ge

end Projection
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.EntropyIntegration.finite_mean_ge_good_fraction
#print axioms BinaryFormMoat.EntropyIntegration.labelledSubsetChoices
#print axioms BinaryFormMoat.EntropyIntegration.labelledSubsetChoices_nonempty
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_eq_choicesMean
#print axioms BinaryFormMoat.GeometryIntegration.labelledSubsetProjection
#print axioms BinaryFormMoat.GeometryIntegration.badLabelledSubsetChoices
#print axioms BinaryFormMoat.GeometryIntegration.badLabelledSubsetFraction
#print axioms BinaryFormMoat.GeometryIntegration.labelledSubsetProjectionEntropyMean
#print axioms BinaryFormMoat.GeometryIntegration.labelledSubsetProjectionEntropyMean_ge
