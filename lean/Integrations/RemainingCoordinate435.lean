import Integrations.DisjointSubset435
import Integrations.RetainedDifferenceEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Exact inclusion probability in a subset of a specified remaining set. -/
theorem relative_powersetCard_mem_fraction {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (r : ℕ) (hr : 1 ≤ r) (hrC : r ≤ C.card) (i : ι) (hi : i ∈ C) :
    ((((C.powersetCard r).filter (fun J => i ∈ J)).card : ℝ) / (C.powersetCard r).card) =
      (r : ℝ) / C.card := by
  have hc : ((C.powersetCard r).filter (fun J => i ∈ J)).card =
      Nat.choose (C.card - 1) (r - 1) := by
    simpa using Finset.card_filter_powersetCard_subset ({i} : Finset ι) C r
      (by simpa using hi) (by simpa using hr)
  have hC : 1 ≤ C.card := hr.trans hrC
  have hm := Nat.add_one_mul_choose_eq (C.card - 1) (r - 1)
  rw [Nat.sub_add_cancel hC, Nat.sub_add_cancel hr] at hm
  rw [hc, Finset.card_powersetCard]
  apply (div_eq_div_iff (by exact_mod_cast (Nat.choose_pos hrC).ne')
    (by exact_mod_cast (by omega : C.card ≠ 0))).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hm)

/-- Uniform sampling inside the remaining set retains its exact coordinate marginal. -/
theorem relativeSubsetMean_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (r : ℕ) (hr : 1 ≤ r) (hrC : r ≤ C.card) (w : ι → ℝ) :
    relativeSubsetMean C r (fun J => ∑ i ∈ J, w i) =
      ((r : ℝ) / C.card) * ∑ i ∈ C, w i := by
  classical
  rw [relativeSubsetMean, sum_subset_weight_by_fibers, Finset.sum_div]
  calc
    _ = ∑ i, if i ∈ C then ((r : ℝ) / C.card) * w i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ C
      · simp only [hi, ite_true]
        calc
          _ = ((((C.powersetCard r).filter (fun J => i ∈ J)).card : ℝ) /
            (C.powersetCard r).card) * w i := by ring
          _ = _ := by rw [relative_powersetCard_mem_fraction C r hr hrC i hi]
      · have he : (C.powersetCard r).filter (fun J => i ∈ J) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro J hJ hiJ
          exact hi ((Finset.mem_powersetCard.mp hJ).1 hiJ)
        simp [hi, he]
    _ = ∑ i ∈ C, ((r : ℝ) / C.card) * w i := by rw [← Finset.sum_filter]; simp
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Conditional tuple subadditivity on a fixed subset with dependent alphabets. -/
theorem condEntropy_subsetObservation_le_sum {Ω ι O : Type*}
    [MeasurableSpace Ω]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    (X : ∀ i, Ω → K i) (hX : ∀ i, Measurable (X i))
    (O : Ω → O) (hO : Measurable O) (J : Finset ι) [FiniteRange O] :
    condEntropy (subsetObservation K X J) O μ ≤ ∑ i ∈ J, condEntropy (X i) O μ := by
  classical
  have h : condEntropy (fun ω (i : J) => X i.val ω) O μ ≤
      ∑ i : J, condEntropy (X i.val) O μ := by
    simp_rw [condEntropy_eq_sum _ _ _ hO]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro o _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (entropy_pi_le_sum (μ[|O ← o]) (fun i : J => K i.val)
        (fun i ω => X i.val ω) (fun i => hX i.val)) measureReal_nonneg
  change condEntropy (subsetObservation K X J) O μ ≤
    ∑ i : J, condEntropy (X i.val) O μ at h
  exact h.trans_eq (Finset.sum_coe_sort J (fun i => condEntropy (X i) O μ))

/-- A mean r-tuple conditional entropy is at most r times the remaining-coordinate mean. -/
theorem relativeSubsetMean_condEntropy_le_remaining {Ω ι O : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    (X : ∀ i, Ω → K i) (O : Ω → O) (C : Finset ι)
    (r : ℕ) (hr : 1 ≤ r) (hrC : r ≤ C.card) :
    relativeSubsetMean C r (fun J => condEntropy (subsetObservation K X J) O μ) ≤
      ((r : ℝ) / C.card) * ∑ i ∈ C, condEntropy (X i) O μ := by
  have h := relativeSubsetMean_mono C r _ _ (fun J _ =>
    condEntropy_subsetObservation_le_sum μ K X (fun _ => measurable_of_finite _)
      O (measurable_of_finite _) J)
  rw [relativeSubsetMean_sum C r hr hrC] at h
  exact h

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.relative_powersetCard_mem_fraction
#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_sum
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_subsetObservation_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_condEntropy_le_remaining
