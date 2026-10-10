import Integrations.SubsetSampling435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def coordinateLogMean {ι R : Type*} [Fintype ι] [Fintype R]
    (K : ι × R → Type*) [∀ c, Fintype (K c)] : ℝ :=
  (∑ c, Real.log (Fintype.card (K c))) / (Fintype.card ι * (Fintype.card R : ℝ))

noncomputable def labelSubsetJointEntropy {Ω ι R : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype R]
    (μ : Measure Ω) (K : ι × R → Type*) [∀ c, MeasurableSpace (K c)]
    (X : ∀ c, Ω → K c) (s : ℕ) : ℝ :=
  subsetLabelAverage s (fun A ρ => entropy (fun ω (i : A) => X (i.1, ρ i.1) ω) μ)

noncomputable def meanCoordinateDeficit {Ω ι R T : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype R] [MeasurableSpace T]
    (μ : Measure Ω) (K : ι × R → Type*) [∀ c, MeasurableSpace (K c)] [∀ c, Fintype (K c)]
    (X : ∀ c, Ω → K c) (Z : Ω → T) : ℝ :=
  (∑ c, (Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ)) /
    (Fintype.card ι * (Fintype.card R : ℝ))

noncomputable def conditionalListDeficit {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S]
    [MeasurableSpace T] [Fintype T]
    (μ : Measure Ω) (X : Ω → S) (Z : Ω → T) (L : T → Finset S) : ℝ :=
  Real.log (Fintype.card S) - Real.log 2 -
    (∑ z, μ.real (Z ⁻¹' {z}) * Real.log ((max 1 (L z).card : ℕ) : ℝ)) -
      μ.real {ω | X ω ∉ L (Z ω)} * Real.log (Fintype.card S)

theorem conditionalListDeficit_le_conditional_deficit {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hZ : Measurable Z) :
    conditionalListDeficit μ X Z L ≤ Real.log (Fintype.card S) - condEntropy X Z μ := by
  unfold conditionalListDeficit
  have h := condEntropy_le_error_aware_list μ X Z L hX hZ
  linarith

section SharedData
variable {Ω ι R T : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Fintype R] [Nonempty R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ι × R → Type*)
  [∀ c, MeasurableSpace (K c)] [∀ c, MeasurableSingletonClass (K c)] [∀ c, Fintype (K c)]
  (X : ∀ c, Ω → K c) (Z : Ω → T) (hX : ∀ c, Measurable (X c)) (hZ : Measurable Z)
include hX hZ

/-- Joint entropy pays for the shared data once, then distributes the cost
using the actual without-replacement subset and uniform-label averages. -/
theorem labelSubsetJointEntropy_sub_shared_le_sum (s : ℕ) (hs : 1 ≤ s)
    (hsk : s ≤ Fintype.card ι) :
    labelSubsetJointEntropy μ K X s - entropy Z μ ≤
      ((s : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ))) *
        ∑ c, condEntropy (X c) Z μ := by
  classical
  have hp : ∀ (A : Finset ι) (ρ : ι → R),
      entropy (fun ω (i : A) => X (i.1, ρ i.1) ω) μ - entropy Z μ ≤
        ∑ i ∈ A, condEntropy (X (i, ρ i)) Z μ := by
    intro A ρ
    have h := entropy_pi_sub_shared_le_condEntropy_sum μ (fun i : A => K (i.1, ρ i.1))
      (fun i ω => X (i.1, ρ i.1) ω) Z (fun i => hX (i.1, ρ i.1)) hZ
    change entropy (fun ω (i : A) => X (i.1, ρ i.1) ω) μ - entropy Z μ ≤
      ∑ i : A, condEntropy (X (i.1, ρ i.1)) Z μ at h
    exact h.trans_eq (Finset.sum_coe_sort A (fun i => condEntropy (X (i, ρ i)) Z μ))
  have h := subsetLabelAverage_mono s
    (fun A ρ => entropy (fun ω (i : A) => X (i.1, ρ i.1) ω) μ - entropy Z μ)
    (fun A ρ => ∑ i ∈ A, condEntropy (X (i, ρ i)) Z μ) (fun A _ ρ => hp A ρ)
  rw [subsetLabelAverage_sub, subsetLabelAverage_const s hsk] at h
  rw [subsetLabelAverage_sum s hs hsk (fun i r => condEntropy (X (i, r)) Z μ)] at h
  simpa only [labelSubsetJointEntropy, Fintype.sum_prod_type] using h

/-- The full shared-conditioning-cost lemma. Gaussian signs are the case
card R = 2; degree-many labels work without any coordinate independence. -/
theorem one_shared_conditioning_cost (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι)
    (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K X s)
    (hdata : entropy Z μ ≤ κ * (s : ℝ) * coordinateLogMean K) :
    meanCoordinateDeficit μ K X Z ≤ (ε + κ) * coordinateLogMean K := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hu := labelSubsetJointEntropy_sub_shared_le_sum μ K X Z hX hZ s hs hsk
  have hl : (1 - ε - κ) * coordinateLogMean K ≤
      (∑ c, condEntropy (X c) Z μ) / (Fintype.card ι * (Fintype.card R : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hspos).mp
    calc
      _ = (1 - ε) * (s : ℝ) * coordinateLogMean K -
          κ * (s : ℝ) * coordinateLogMean K := by ring
      _ ≤ labelSubsetJointEntropy μ K X s - entropy Z μ := by linarith
      _ ≤ _ := by convert hu using 1; ring
  unfold meanCoordinateDeficit
  rw [Finset.sum_sub_distrib, sub_div]
  change coordinateLogMean K - _ ≤ (ε + κ) * coordinateLogMean K
  nlinarith only [hl]

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- List/error lower certificates cannot exceed the shared joint deficit
budget. Success events may depend on both residue and data. -/
theorem shared_data_error_aware_list_budget (s : ℕ) (hs : 1 ≤ s)
    (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K X s)
    (hdata : entropy Z μ ≤ κ * (s : ℝ) * coordinateLogMean K)
    (L : ∀ c, T → Finset (K c)) :
    (∑ c, conditionalListDeficit μ (X c) Z (L c)) /
      (Fintype.card ι * (Fintype.card R : ℝ)) ≤ (ε + κ) * coordinateLogMean K := by
  apply le_trans _ (one_shared_conditioning_cost μ K X Z hX hZ s hs hsk ε κ hjoint hdata)
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact Finset.sum_le_sum (fun c _ =>
    conditionalListDeficit_le_conditional_deficit μ (X c) Z (L c) (hX c) hZ)

omit [MeasurableSpace Bool] [MeasurableSingletonClass Bool] in
/-- An explicit fraction bound for coordinates having a large deficit. -/
theorem shared_data_few_high_deficit_coordinates (s : ℕ) (hs : 1 ≤ s)
    (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K X s)
    (hdata : entropy Z μ ≤ κ * (s : ℝ) * coordinateLogMean K)
    (B : Finset (ι × R)) (a : ℝ) (ha : 0 < a)
    (hB : ∀ c ∈ B, a ≤ Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ) :
    (B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ)) ≤
      ((ε + κ) * coordinateLogMean K) / a := by
  classical
  have hsum : a * (B.card : ℝ) ≤
      ∑ c, (Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ) := by
    calc
      _ = ∑ c ∈ B, a := by simp [mul_comm]
      _ ≤ ∑ c ∈ B, (Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ) :=
        Finset.sum_le_sum hB
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun c _ _ => conditional_coordinate_deficit_nonneg μ (X c) Z)
  apply (le_div_iff₀ ha).mpr
  calc
    _ = (a * (B.card : ℝ)) / (Fintype.card ι * (Fintype.card R : ℝ)) := by ring
    _ ≤ meanCoordinateDeficit μ K X Z := div_le_div_of_nonneg_right hsum
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ _ := one_shared_conditioning_cost μ K X Z hX hZ s hs hsk ε κ hjoint hdata

end SharedData

theorem coordinateLogMean_eq_of_label_invariant {ι R : Type*}
    [Fintype ι] [Fintype R] [Nonempty R]
    (K : ι × R → Type*) [∀ c, Fintype (K c)] (p : ι → ℕ)
    (hcard : ∀ i r, Fintype.card (K (i, r)) = p i) :
    coordinateLogMean K = (∑ i, Real.log (p i : ℝ)) / Fintype.card ι := by
  have hd : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold coordinateLogMean
  rw [Fintype.sum_prod_type]
  simp_rw [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp [hd]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.conditionalListDeficit_le_conditional_deficit
#print axioms BinaryFormMoat.EntropyIntegration.labelSubsetJointEntropy_sub_shared_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.one_shared_conditioning_cost
#print axioms BinaryFormMoat.EntropyIntegration.shared_data_error_aware_list_budget
#print axioms BinaryFormMoat.EntropyIntegration.shared_data_few_high_deficit_coordinates
#print axioms BinaryFormMoat.EntropyIntegration.coordinateLogMean_eq_of_label_invariant
