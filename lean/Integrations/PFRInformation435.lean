import Integrations.PFRList435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-! Information gained from a list certificate under the specified law.
The conditional versions retain the entropy after prior observations;
uniformity or independence after conditioning is never inferred. -/

/-- The error penalty uses the true finite support, rather than the ambient
alphabet. In particular d roots in ZMod p cost log d on a failure branch. -/
theorem condEntropy_le_list_size_error_of_ae_support {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (A : Finset S) (hA : A.Nonempty) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hsupport : ∀ᵐ ω ∂μ, X ω ∈ A)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ ε) :
    condEntropy X Y μ ≤ Real.log 2 + Real.log (M : ℝ) + ε * Real.log (A.card : ℝ) := by
  classical
  let E := listErrorFlag X Y L
  let Z := fun ω => (E ω, Y ω)
  have hE : Measurable E := measurable_listErrorFlag X Y L hX hY
  have hZ : Measurable Z := hE.prodMk hY
  have ht : (∑ y, μ.real (Z ⁻¹' {(true, y)}) * entropy X (μ[|Z ← (true, y)])) ≤
      μ.real (E ⁻¹' {true}) * Real.log (A.card : ℝ) := by
    calc
      _ ≤ ∑ y, μ.real (Z ⁻¹' {(true, y)}) * Real.log (A.card : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        exact entropy_le_log_card_of_mem hX
          (hsupport.filter_mono cond_absolutelyContinuous.ae_le)
      _ = _ := by rw [← Finset.sum_mul, sum_pair_fiber_real μ E Y hE hY true]
  have hf : (∑ y, μ.real (Z ⁻¹' {(false, y)}) * entropy X (μ[|Z ← (false, y)])) ≤
      Real.log (M : ℝ) := by
    calc
      _ ≤ ∑ y, μ.real (Z ⁻¹' {(false, y)}) * Real.log (M : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        apply (success_fiber_entropy_le μ X Y E L hX hY hE
          (listErrorFlag_false_mem X Y L) y).trans
        apply Real.log_le_log
        · exact_mod_cast (show 0 < max 1 (L y).card by omega)
        · exact_mod_cast max_le hM (hsize y)
      _ = μ.real (E ⁻¹' {false}) * Real.log (M : ℝ) := by
        rw [← Finset.sum_mul, sum_pair_fiber_real μ E Y hE hY false]
      _ ≤ 1 * Real.log (M : ℝ) := mul_le_mul_of_nonneg_right
        measureReal_le_one (Real.log_nonneg (by exact_mod_cast hM))
      _ = _ := one_mul _
  have hb : condEntropy X Z μ ≤ Real.log (M : ℝ) +
      μ.real (E ⁻¹' {true}) * Real.log (A.card : ℝ) := by
    rw [condEntropy_eq_sum_fintype X Z μ hZ, Fintype.sum_prod_type, Fintype.sum_bool]
    linarith
  have hflag := condEntropy_le_error_flag μ X Y E hX hY hE
  change condEntropy X Y μ ≤ Real.log 2 + condEntropy X Z μ at hflag
  have he : μ.real (E ⁻¹' {true}) ≤ ε := by
    simpa only [E, listErrorFlag_true_preimage] using herr
  have hlog : 0 ≤ Real.log (A.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ A.card from hA.card_pos))
  have he' := mul_le_mul_of_nonneg_right he hlog
  linarith

theorem mutualInfo_ge_error_aware_list {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) :
    entropy X μ - Real.log 2 -
      (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) -
      μ.real {ω | X ω ∉ L (Y ω)} * Real.log (Fintype.card S) ≤ mutualInfo X Y μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  have h := condEntropy_le_error_aware_list μ X Y L hX hY
  linarith

theorem mutualInfo_ge_list_size_error {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ ε) :
    entropy X μ - Real.log 2 - Real.log (M : ℝ) -
      ε * Real.log (Fintype.card S) ≤ mutualInfo X Y μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  have h := condEntropy_le_list_size_error μ X Y L hX hY M hM hsize ε herr
  linarith

theorem uniform_mutualInfo_ge_list_size_error {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (K : Finset S) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (huniform : IsUniform K X μ)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ ε) :
    Real.log (K.card : ℝ) - Real.log 2 - Real.log (M : ℝ) -
      ε * Real.log (Fintype.card S) ≤ mutualInfo X Y μ := by
  have h := mutualInfo_ge_list_size_error μ X Y L hX hY M hM hsize ε herr
  simpa only [huniform.entropy_eq hX, Nat.card_eq_fintype_card, Fintype.card_coe] using h

theorem uniform_mutualInfo_ge_list_size_error_on_support {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (K : Finset S) (hK : K.Nonempty) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (huniform : IsUniform K X μ)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ ε) :
    (1 - ε) * Real.log (K.card : ℝ) - Real.log 2 - Real.log (M : ℝ) ≤
      mutualInfo X Y μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY, huniform.entropy_eq hX]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h := condEntropy_le_list_size_error_of_ae_support μ X Y K hK L hX hY
    huniform.ae_mem M hM hsize ε herr
  linarith

theorem condMutualInfo_ge_list_size_error {Ω S T U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (L : T × U → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω, Z ω)} ≤ ε) :
    condEntropy X Z μ - Real.log 2 - Real.log (M : ℝ) -
      ε * Real.log (Fintype.card S) ≤ condMutualInfo X Y Z μ := by
  rw [condMutualInfo_eq' hX hY hZ]
  have h := condEntropy_le_list_size_error μ X (fun ω => (Y ω, Z ω)) L
    hX (hY.prodMk hZ) M hM hsize ε herr
  linarith

theorem condMutualInfo_ge_list_size_error_of_ae_support {Ω S T U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (A : Finset S) (hA : A.Nonempty)
    (L : T × U → Finset S) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hsupport : ∀ᵐ ω ∂μ, X ω ∈ A) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω, Z ω)} ≤ ε) :
    condEntropy X Z μ - Real.log 2 - Real.log (M : ℝ) -
      ε * Real.log (A.card : ℝ) ≤ condMutualInfo X Y Z μ := by
  rw [condMutualInfo_eq' hX hY hZ]
  have h := condEntropy_le_list_size_error_of_ae_support μ X (fun ω => (Y ω, Z ω)) A hA L
    hX (hY.prodMk hZ) hsupport M hM hsize ε herr
  linarith

/-- Independence of the prior observation is an explicit premise. -/
theorem condMutualInfo_ge_list_size_error_of_indep {Ω S T U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (L : T × U → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hindep : IndepFun X Z μ)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω, Z ω)} ≤ ε) :
    entropy X μ - Real.log 2 - Real.log (M : ℝ) -
      ε * Real.log (Fintype.card S) ≤ condMutualInfo X Y Z μ := by
  simpa only [hindep.condEntropy_eq_entropy hX hZ] using
    condMutualInfo_ge_list_size_error μ X Y Z L hX hY hZ M hM hsize ε herr

theorem conditioned_mutualInfo_ge_list_size_error {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (B : Set Ω) (hB : MeasurableSet B)
    (hpos : 0 < μ.real B) (δ : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ δ) :
    entropy X (μ[|B]) - Real.log 2 - Real.log (M : ℝ) -
      (δ / μ.real B) * Real.log (Fintype.card S) ≤ mutualInfo X Y (μ[|B]) := by
  let : IsProbabilityMeasure μ[|B] := cond_isProbabilityMeasure_of_real (ne_of_gt hpos)
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  have h := conditioned_condEntropy_le_list_size_error μ X Y L hX hY M hM hsize
    B hB hpos δ herr
  linarith

theorem mutualInfo_le_observation_log_card {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T)
    (hX : Measurable X) (hY : Measurable Y) :
    mutualInfo X Y μ ≤ Real.log (Fintype.card T) := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY]
  have h := entropy_le_log_card Y μ
  have hn := condEntropy_nonneg Y X μ
  linarith

/-- Shared prior data is paid for once, with no independence hypothesis. -/
theorem condEntropy_ge_entropy_sub_observation_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T)
    (hX : Measurable X) (hZ : Measurable Z) :
    entropy X μ - entropy Z μ ≤ condEntropy X Z μ := by
  rw [chain_rule'' μ hX hZ, chain_rule' μ hX hZ]
  have hn := condEntropy_nonneg Z X μ
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_list_size_error_of_ae_support
#print axioms BinaryFormMoat.EntropyIntegration.mutualInfo_ge_error_aware_list
#print axioms BinaryFormMoat.EntropyIntegration.mutualInfo_ge_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.uniform_mutualInfo_ge_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.uniform_mutualInfo_ge_list_size_error_on_support
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_ge_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_ge_list_size_error_of_ae_support
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_ge_list_size_error_of_indep
#print axioms BinaryFormMoat.EntropyIntegration.conditioned_mutualInfo_ge_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.mutualInfo_le_observation_log_card
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_ge_entropy_sub_observation_entropy
