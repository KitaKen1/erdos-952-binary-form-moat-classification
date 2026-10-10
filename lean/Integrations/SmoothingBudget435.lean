import Integrations.TerminalEntropy435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- A small-probability entropy bound uniform all the way down to zero.
It uses the scaled `negMulLog` tangent inequality, avoiding a new
derivative/monotonicity development for binary entropy. -/
theorem successEntropyCost_le_small_budget (ε δ : ℝ)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    successEntropyCost ε ≤ δ * (1 - Real.log δ) := by
  have hmul : δ * (ε / δ) = ε := by field_simp [hδ.ne']
  have hn : (ε / δ) * Real.negMulLog δ = -ε * Real.log δ := by
    rw [Real.negMulLog_eq_neg]
    field_simp [hδ.ne']
  have hi := Real.negMulLog_mul δ (ε / δ)
  rw [hmul, hn] at hi
  have ht := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hε hδ.le)) hδ.le
  have hd : δ * (1 - ε / δ) = δ - ε := by rw [mul_sub, mul_one, hmul]
  rw [hd] at ht
  have hc := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (hεδ.trans hδ1))
  have hl := mul_le_mul_of_nonpos_right hεδ (Real.log_nonpos hδ.le hδ1)
  unfold successEntropyCost
  nlinarith

theorem smoothing_entropy_cost_le_small_budget (ε δ B : ℝ)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    successEntropyCost ε + ε * B ≤ δ * (1 - Real.log δ + B) := by
  have h := successEntropyCost_le_small_budget ε δ hε hεδ hδ hδ1
  have hm := mul_le_mul_of_nonneg_right hεδ hB
  nlinarith

theorem terminal_shift_le_length (a N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) : a ≤ N := by
  have hp : T ≤ T ^ 10 := by
    have hpow : 1 ≤ T ^ 9 := one_le_pow₀ hT
    calc
      T = T * 1 := by ring
      _ ≤ T * T ^ 9 := mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = T ^ 10 := by ring
  exact_mod_cast ha.trans (hp.trans hN)

/-- Explicit source-scale error; there is no fixed log(2) loss. -/
theorem terminal_smoothing_entropy_source_budget (a N : ℕ) (T B : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) (hB : 0 ≤ B) :
    successEntropyCost ((a : ℝ) / N) + (a : ℝ) / N * B ≤
      (1 + 9 * Real.log T + B) / T ^ 9 := by
  have hTp : 0 < T := by linarith
  have hδ : 0 < 1 / T ^ 9 := one_div_pos.mpr (pow_pos hTp 9)
  have hδ1 : 1 / T ^ 9 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hTp 9)).mpr
    simpa using (one_le_pow₀ hT : (1 : ℝ) ≤ T ^ 9)
  have h := smoothing_entropy_cost_le_small_budget ((a : ℝ) / N) (1 / T ^ 9) B
    (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg N))
    (terminal_shift_ratio_source_bound a N T hTp ha hN) hδ hδ1 hB
  have hl : Real.log (1 / T ^ 9) = -9 * Real.log T := by
    rw [Real.log_div one_ne_zero (pow_ne_zero 9 hTp.ne'), Real.log_one, Real.log_pow]
    norm_num
  rw [hl] at h
  convert h using 1
  ring

section Source
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

/-- Source-scale conditional entropy comparison, instantiated on the actual
terminal law with its tenth-power uniform-offset length. -/
theorem smoothedTimeLaw_condEntropy_source_bound {S U : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (X : ℕ → S) (Z : ℕ → U) (a : ℕ) (T : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |condEntropy (fun t => X (t + a)) (fun t => Z (t + a)) (smoothedTimeLaw μ b N) -
      condEntropy X Z (smoothedTimeLaw μ b N)| ≤
      (1 + 9 * Real.log T + Real.log (Fintype.card S)) / T ^ 9 := by
  have hlog : 0 ≤ Real.log (Fintype.card S) := by
    by_cases hs : Fintype.card S = 0
    · simp [hs]
    · apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ Fintype.card S)
  exact (smoothedTimeLaw_condEntropy_shift_bound μ b N X Z a
    (terminal_shift_le_length a N T hT ha hN)).trans
      (terminal_smoothing_entropy_source_budget a N T _ hT ha hN hlog)

theorem smoothedTimeLaw_condMutualInfo_source_bound {S U V : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (X : ℕ → S) (Y : ℕ → U) (Z : ℕ → V) (a : ℕ) (T : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |condMutualInfo (fun t => X (t + a)) (fun t => Y (t + a)) (fun t => Z (t + a))
        (smoothedTimeLaw μ b N) - condMutualInfo X Y Z (smoothedTimeLaw μ b N)| ≤
      2 * ((1 + 9 * Real.log T + Real.log (Fintype.card S)) / T ^ 9) := by
  have h₀ := smoothedTimeLaw_condEntropy_source_bound μ b N X Z a T hT ha hN
  have h₁ := smoothedTimeLaw_condEntropy_source_bound μ b N X (fun t => (Y t, Z t)) a T hT ha hN
  rw [condMutualInfo_eq' (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) _, condMutualInfo_eq' (measurable_of_countable _)
    (measurable_of_countable _) (measurable_of_countable _) _, abs_le]
  have hb₀ := abs_le.mp h₀
  have hb₁ := abs_le.mp h₁
  constructor <;> linarith [hb₀.1, hb₀.2, hb₁.1, hb₁.2]

theorem smoothedTimeLaw_word_condEntropy_source_bound {K U : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (L : ℕ) (W : ℕ → (Fin L → K)) (Z : ℕ → U) (a : ℕ) (T : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |condEntropy (fun t => W (t + a)) (fun t => Z (t + a)) (smoothedTimeLaw μ b N) -
      condEntropy W Z (smoothedTimeLaw μ b N)| ≤
      (1 + 9 * Real.log T + L * Real.log (Fintype.card K)) / T ^ 9 := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using
    smoothedTimeLaw_condEntropy_source_bound μ b N W Z a T hT ha hN

/-- Use information symmetry to charge the word alphabet, rather than the
potentially much larger residue or auxiliary alphabets. -/
theorem smoothedTimeLaw_word_information_source_bound {K U V : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (L : ℕ) (W : ℕ → (Fin L → K)) (Y : ℕ → U) (Z : ℕ → V) (a : ℕ) (T : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |condMutualInfo (fun t => Y (t + a)) (fun t => W (t + a)) (fun t => Z (t + a))
        (smoothedTimeLaw μ b N) - condMutualInfo Y W Z (smoothedTimeLaw μ b N)| ≤
      2 * ((1 + 9 * Real.log T + L * Real.log (Fintype.card K)) / T ^ 9) := by
  rw [condMutualInfo_comm (measurable_of_countable _) (measurable_of_countable _)
    (fun t => Z (t + a)) _, condMutualInfo_comm (measurable_of_countable _)
    (measurable_of_countable _) Z _]
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using
    smoothedTimeLaw_condMutualInfo_source_bound μ b N W Y Z a T hT ha hN

/-- The source estimate under an actual positive-mass earlier checkpoint. -/
theorem smoothedTimeLaw_cond_checkpoint_entropy_source_bound {A S U : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (V : Ω → A) (v : A) (hv : μ (V ⁻¹' {v}) ≠ 0)
    (X : ℕ → S) (Z : ℕ → U) (a : ℕ) (T : ℝ)
    (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |condEntropy (fun t => X (t + a)) (fun t => Z (t + a))
        (smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N) -
      condEntropy X Z (smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N)| ≤
      (1 + 9 * Real.log T + Real.log (Fintype.card S)) / T ^ 9 := by
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact smoothedTimeLaw_condEntropy_source_bound (μ[|V ⁻¹' {v}]) b N X Z a T hT ha hN

end Source

/-- Constructed-length version: no uniform-offset budget is postulated. -/
theorem smoothedTimeLaw_condEntropy_ceiling_source_bound {Ω S U : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
    (X : ℕ → S) (Z : ℕ → U) (a : ℕ) (T : ℝ) (hT : 1 ≤ T) (ha : (a : ℝ) ≤ T) :
    |condEntropy (fun t => X (t + a)) (fun t => Z (t + a))
        (smoothedTimeLaw μ b (terminalSmoothingLength T)) -
      condEntropy X Z (smoothedTimeLaw μ b (terminalSmoothingLength T))| ≤
      (1 + 9 * Real.log T + Real.log (Fintype.card S)) / T ^ 9 := by
  have : NeZero (terminalSmoothingLength T) := ⟨(terminalSmoothingLength_pos T).ne'⟩
  exact smoothedTimeLaw_condEntropy_source_bound μ b (terminalSmoothingLength T) X Z a T
    hT ha (terminalSmoothingLength_ge T)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.successEntropyCost_le_small_budget
#print axioms BinaryFormMoat.EntropyIntegration.smoothing_entropy_cost_le_small_budget
#print axioms BinaryFormMoat.EntropyIntegration.terminal_shift_le_length
#print axioms BinaryFormMoat.EntropyIntegration.terminal_smoothing_entropy_source_budget
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condEntropy_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condMutualInfo_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_condEntropy_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_information_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_cond_checkpoint_entropy_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condEntropy_ceiling_source_bound
