import Integrations.SharedData435
import Integrations.SuccessAverage435
import Integrations.EmpiricalLists435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def smallListSuccess {Ω S T : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → S) (Z : Ω → T) (L : T → Finset S) (M : ℕ) : ℝ :=
  μ.real {ω | X ω ∈ L (Z ω) ∧ (L (Z ω)).card ≤ M}

theorem smallListSuccess_mem_unitInterval {Ω S T : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T)
    (L : T → Finset S) (M : ℕ) :
    smallListSuccess μ X Z L M ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  exact (measureReal_mono (μ := μ) (Set.subset_univ _)).trans_eq probReal_univ

/-- Membership can be common across coordinates while list-size failures
are controlled only on average. No success/size independence is assumed. -/
theorem mean_smallListSuccess_ge_of_list_failure {Ω C T : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : C → Type*) (X : ∀ c, Ω → K c) (Z : Ω → T)
    (B : Finset C) (hB : B.Nonempty) (L : ∀ c, T → Finset (K c)) (M : C → ℕ) (δ : ℝ)
    (htrue : ∀ c ∈ B, δ ≤ μ.real {ω | X c ω ∈ L c (Z ω)})
    (hbad : finiteRealMean B (fun c => μ.real {ω | M c < (L c (Z ω)).card}) ≤ δ / 2) :
    δ / 2 ≤ finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c)) := by
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have hs : ∑ c ∈ B, (δ - μ.real {ω | M c < (L c (Z ω)).card}) ≤
      ∑ c ∈ B, smallListSuccess μ (X c) Z (L c) (M c) := by
    apply Finset.sum_le_sum
    intro c hmem
    exact (sub_le_sub_right (htrue c hmem) _).trans
      (success_with_small_list μ (X c) Z (L c) (M c))
  have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg B.card)
  have he : (∑ c ∈ B, δ) / (B.card : ℝ) = δ := by simp [nsmul_eq_mul, hc]
  rw [Finset.sum_sub_distrib, sub_div, he] at h
  change δ - finiteRealMean B (fun c => μ.real {ω | M c < (L c (Z ω)).card}) ≤
    finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c)) at h
  linarith only [h, hbad]

section Coordinates
variable {Ω C T : Type*} [MeasurableSpace Ω]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (K : C → Type*)
  [∀ c, MeasurableSpace (K c)] [∀ c, MeasurableSingletonClass (K c)] [∀ c, Fintype (K c)]
  (X : ∀ c, Ω → K c) (Z : Ω → T) (hX : ∀ c, Measurable (X c)) (hZ : Measurable Z)
include hX hZ

/-- The averaged rare-success inequality applies to actual capped-list
events, without assuming that the successes are independent of data. -/
theorem mean_conditional_deficit_ge_small_list_success
    (B : Finset C) (hB : B.Nonempty) (L : ∀ c, T → Finset (K c)) (M : C → ℕ)
    (hM : ∀ c ∈ B, 1 ≤ M c) (G : ℝ)
    (hgap : ∀ c ∈ B, G ≤ Real.log (Fintype.card (K c)) - Real.log (M c : ℝ)) :
    finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c)) * G -
      successEntropyCost
        (finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c))) ≤
      finiteRealMean B (fun c => Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ) := by
  apply finiteRealMean_deficit_ge_success B hB
    (fun c => smallListSuccess μ (X c) Z (L c) (M c))
    (fun c => Real.log (Fintype.card (K c)) - Real.log (M c : ℝ)) _ G
    (fun c _ => smallListSuccess_mem_unitInterval μ (X c) Z (L c) (M c)) hgap
  intro c hc
  exact conditional_deficit_ge_small_list_success μ (X c) Z (L c) (hX c) hZ (M c) (hM c hc)

theorem mean_conditional_deficit_ge_coverage_scale
    (B : Finset C) (hB : B.Nonempty) (L : ∀ c, T → Finset (K c)) (M : C → ℕ)
    (hM : ∀ c ∈ B, 1 ≤ M c) (δ β logT : ℝ)
    (hδ : 0 < δ) (hβ : 0 ≤ β) (hT : 0 ≤ logT)
    (hmean : δ / 2 ≤ finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c)))
    (hgap : ∀ c ∈ B, β / 2 * logT ≤
      Real.log (Fintype.card (K c)) - Real.log (M c : ℝ))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β / 4 * logT) :
    δ * β / 8 * logT ≤
      finiteRealMean B (fun c => Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ) := by
  apply finiteRealMean_deficit_ge_coverage_scale B hB
    (fun c => smallListSuccess μ (X c) Z (L c) (M c))
    (fun c => Real.log (Fintype.card (K c)) - Real.log (M c : ℝ)) _ δ β logT
    hδ hβ hT (fun c _ => smallListSuccess_mem_unitInterval μ (X c) Z (L c) (M c))
    hmean hgap _ hlog
  intro c hc
  exact conditional_deficit_ge_small_list_success μ (X c) Z (L c) (hX c) hZ (M c) (hM c hc)

end Coordinates

section SharedCoverage
variable {Ω ι R T : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Fintype R] [Nonempty R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ι × R → Type*)
  [∀ c, MeasurableSpace (K c)] [∀ c, MeasurableSingletonClass (K c)] [∀ c, Fintype (K c)]
  (X : ∀ c, Ω → K c) (Z : Ω → T) (hX : ∀ c, Measurable (X c)) (hZ : Measurable Z)
include hX hZ

/-- Final entropy-budget consequence of the source's coverage argument.
The actual posterior experiment, mean success, list gap, geometric joint
entropy and shared-data size are premises, not conclusions of this adapter. -/
theorem shared_data_few_small_list_coordinates
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K X s)
    (hdata : entropy Z μ ≤ κ * (s : ℝ) * coordinateLogMean K)
    (B : Finset (ι × R)) (hB : B.Nonempty)
    (L : ∀ c, T → Finset (K c)) (M : ι × R → ℕ) (hM : ∀ c ∈ B, 1 ≤ M c)
    (δ β logT η : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (hT : 0 < logT)
    (hmean : δ / 2 ≤ finiteRealMean B (fun c => smallListSuccess μ (X c) Z (L c) (M c)))
    (hgap : ∀ c ∈ B, β / 2 * logT ≤
      Real.log (Fintype.card (K c)) - Real.log (M c : ℝ))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β / 4 * logT)
    (hscale : coordinateLogMean K ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β / 16) :
    (B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  classical
  let D := fun c => Real.log (Fintype.card (K c)) - condEntropy (X c) Z μ
  let t := δ * β / 8 * logT
  have ht : 0 < t := mul_pos (div_pos (mul_pos hδ hβ) (by norm_num)) hT
  have hlow := mean_conditional_deficit_ge_coverage_scale μ K X Z hX hZ
    B hB L M hM δ β logT hδ hβ.le hT.le hmean hgap hlog
  have hcard : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsumB : t * (B.card : ℝ) ≤ ∑ c ∈ B, D c :=
    (le_div_iff₀ hcard).mp hlow
  have hsum : t * (B.card : ℝ) ≤ ∑ c, D c := hsumB.trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun c _ _ => conditional_coordinate_deficit_nonneg μ (X c) Z))
  have hbound : ((B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ))) * t ≤
      (ε + κ) * coordinateLogMean K := by
    calc
      _ = (t * (B.card : ℝ)) / (Fintype.card ι * (Fintype.card R : ℝ)) := by ring
      _ ≤ meanCoordinateDeficit μ K X Z := div_le_div_of_nonneg_right hsum
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ ≤ _ := one_shared_conditioning_cost μ K X Z hX hZ s hs hsk ε κ hjoint hdata
  have hupper : (ε + κ) * coordinateLogMean K ≤ η * t := by
    calc
      _ ≤ (ε + κ) * (2 * logT) := mul_le_mul_of_nonneg_left hscale hcost
      _ ≤ (η * δ * β / 16) * (2 * logT) :=
        mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := by dsimp [t]; ring
  exact (mul_le_mul_iff_right₀ ht).mp
    (by simpa only [mul_comm] using hbound.trans hupper)

end SharedCoverage
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.smallListSuccess_mem_unitInterval
#print axioms BinaryFormMoat.EntropyIntegration.mean_smallListSuccess_ge_of_list_failure
#print axioms BinaryFormMoat.EntropyIntegration.mean_conditional_deficit_ge_small_list_success
#print axioms BinaryFormMoat.EntropyIntegration.mean_conditional_deficit_ge_coverage_scale
#print axioms BinaryFormMoat.EntropyIntegration.shared_data_few_small_list_coordinates
