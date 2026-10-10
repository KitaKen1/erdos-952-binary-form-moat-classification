import Integrations.PFRList435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The actual Boolean entropy cost, written without an additional
binary-entropy library dependency. -/
noncomputable def successEntropyCost (a : ℝ) : ℝ :=
  Real.negMulLog a + Real.negMulLog (1 - a)

theorem bool_false_true_mass {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω → Bool) (hE : Measurable E) :
    μ.real (E ⁻¹' {true}) = 1 - μ.real (E ⁻¹' {false}) := by
  have he : E ⁻¹' {true} = (E ⁻¹' {false})ᶜ := by
    ext ω
    cases E ω <;> simp
  rw [he, measureReal_compl (hE (MeasurableSet.singleton false)), probReal_univ]

theorem entropy_bool_eq_successEntropyCost {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω → Bool) (hE : Measurable E) :
    entropy E μ = successEntropyCost (μ.real (E ⁻¹' {false})) := by
  rw [entropy_eq_sum μ, tsum_fintype, Fintype.sum_bool]
  simp_rw [map_measureReal_apply hE (MeasurableSet.singleton _)]
  rw [bool_false_true_mass μ E hE]
  simp only [successEntropyCost, add_comm]

theorem successEntropyCost_le_log_bound (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    successEntropyCost a ≤ a * Real.log (Real.exp 1 / a) := by
  have h := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr ha1)
  unfold successEntropyCost
  rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt ha), Real.log_exp]
  simp only [Real.negMulLog] at h ⊢
  linarith

theorem condEntropy_le_flag_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T) (E : Ω → Bool)
    (hX : Measurable X) (hZ : Measurable Z) (hE : Measurable E) :
    condEntropy X Z μ ≤ entropy E μ + condEntropy X (fun ω => (E ω, Z ω)) μ := by
  have hfirst := cond_chain_rule' μ hX hE hZ
  have hsecond := cond_chain_rule μ hX hE hZ
  have hn := condEntropy_nonneg E (fun ω => (X ω, Z ω)) μ
  have he := condEntropy_le_entropy μ hE hZ
  linarith

/-- Keep the success fiber's actual mass instead of replacing it by the
full observation mass. This is the rare-success short-list inequality. -/
theorem condEntropy_le_success_list {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T)
    (E : Ω → Bool) (L : T → Finset S) (hX : Measurable X) (hZ : Measurable Z)
    (hE : Measurable E) (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ z, (L z).card ≤ M)
    (hgood : ∀ ω, E ω = false → X ω ∈ L (Z ω)) :
    condEntropy X Z μ ≤ successEntropyCost (μ.real (E ⁻¹' {false})) +
      μ.real (E ⁻¹' {false}) * Real.log (M : ℝ) +
      (1 - μ.real (E ⁻¹' {false})) * Real.log (Fintype.card S) := by
  classical
  let W := fun ω => (E ω, Z ω)
  have hW : Measurable W := hE.prodMk hZ
  have hf : (∑ z, μ.real (W ⁻¹' {(false, z)}) * entropy X (μ[|W ← (false, z)])) ≤
      μ.real (E ⁻¹' {false}) * Real.log (M : ℝ) := by
    calc
      _ ≤ ∑ z, μ.real (W ⁻¹' {(false, z)}) * Real.log (M : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        apply (success_fiber_entropy_le μ X Z E L hX hZ hE hgood z).trans
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < max 1 (L z).card))
          (by exact_mod_cast (max_le hM (hsize z)))
      _ = _ := by rw [← Finset.sum_mul, sum_pair_fiber_real μ E Z hE hZ false]
  have ht : (∑ z, μ.real (W ⁻¹' {(true, z)}) * entropy X (μ[|W ← (true, z)])) ≤
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
    calc
      _ ≤ ∑ z, μ.real (W ⁻¹' {(true, z)}) * Real.log (Fintype.card S) := by
        exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left
          (entropy_le_log_card X _) measureReal_nonneg)
      _ = _ := by rw [← Finset.sum_mul, sum_pair_fiber_real μ E Z hE hZ true]
  have hb : condEntropy X W μ ≤ μ.real (E ⁻¹' {false}) * Real.log (M : ℝ) +
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
    rw [condEntropy_eq_sum_fintype X W μ hW, Fintype.sum_prod_type, Fintype.sum_bool]
    linarith
  have h := condEntropy_le_flag_entropy μ X Z E hX hZ hE
  rw [entropy_bool_eq_successEntropyCost μ E hE] at h
  rw [bool_false_true_mass μ E hE] at hb
  change condEntropy X Z μ ≤ _ at h
  linarith

theorem conditional_deficit_ge_success_list {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T)
    (E : Ω → Bool) (L : T → Finset S) (hX : Measurable X) (hZ : Measurable Z)
    (hE : Measurable E) (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ z, (L z).card ≤ M)
    (hgood : ∀ ω, E ω = false → X ω ∈ L (Z ω)) :
    μ.real (E ⁻¹' {false}) * (Real.log (Fintype.card S) - Real.log (M : ℝ)) -
      successEntropyCost (μ.real (E ⁻¹' {false})) ≤
        Real.log (Fintype.card S) - condEntropy X Z μ := by
  have h := condEntropy_le_success_list μ X Z E L hX hZ hE M hM hsize hgood
  nlinarith only [h]

def cappedList {S T : Type*} (L : T → Finset S) (M : ℕ) (z : T) : Finset S :=
  if (L z).card ≤ M then L z else ∅

theorem cappedList_card_le {S T : Type*} (L : T → Finset S) (M : ℕ) (z : T) :
    (cappedList L M z).card ≤ M := by
  unfold cappedList
  split_ifs with h
  · exact h
  · simp

theorem cappedList_success_preimage {Ω S T : Type*}
    (X : Ω → S) (Z : Ω → T) (L : T → Finset S) (M : ℕ) :
    listErrorFlag X Z (cappedList L M) ⁻¹' {false} =
      {ω | X ω ∈ L (Z ω) ∧ (L (Z ω)).card ≤ M} := by
  classical
  ext ω
  by_cases hs : (L (Z ω)).card ≤ M <;> simp [listErrorFlag, cappedList, hs]

/-- The short-list lower bound uses the joint success-and-size event,
which may depend on both the residue and common data. -/
theorem conditional_deficit_ge_small_list_success {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T)
    (L : T → Finset S) (hX : Measurable X) (hZ : Measurable Z)
    (M : ℕ) (hM : 1 ≤ M) :
    let a := μ.real {ω | X ω ∈ L (Z ω) ∧ (L (Z ω)).card ≤ M}
    a * (Real.log (Fintype.card S) - Real.log (M : ℝ)) - successEntropyCost a ≤
      Real.log (Fintype.card S) - condEntropy X Z μ := by
  have h := conditional_deficit_ge_success_list μ X Z
    (listErrorFlag X Z (cappedList L M)) (cappedList L M) hX hZ
    (measurable_listErrorFlag X Z (cappedList L M) hX hZ) M hM
    (cappedList_card_le L M) (listErrorFlag_false_mem X Z (cappedList L M))
  simpa only [cappedList_success_preimage] using h

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.bool_false_true_mass
#print axioms BinaryFormMoat.EntropyIntegration.entropy_bool_eq_successEntropyCost
#print axioms BinaryFormMoat.EntropyIntegration.successEntropyCost_le_log_bound
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_flag_entropy
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_success_list
#print axioms BinaryFormMoat.EntropyIntegration.conditional_deficit_ge_success_list
#print axioms BinaryFormMoat.EntropyIntegration.cappedList_card_le
#print axioms BinaryFormMoat.EntropyIntegration.cappedList_success_preimage
#print axioms BinaryFormMoat.EntropyIntegration.conditional_deficit_ge_small_list_success
