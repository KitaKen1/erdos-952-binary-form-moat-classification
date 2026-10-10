import Integrations.TerminalSmoothing435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Checkpoint
variable {Ω A : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A)
  (b : Ω → ℕ) (N : ℕ) [NeZero N]

omit [IsProbabilityMeasure μ] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSingletonClass Ω] in
/-- Conditioning on an earlier source checkpoint leaves the fresh uniform
offset independent. This identity also covers zero-mass fibers. -/
theorem independentOffset_cond_checkpoint (v : A) :
    (μ.prod (uniformOn (Set.univ : Set (Fin N))))[|(fun ω => V ω.1) ⁻¹' {v}] =
      (μ[|V ⁻¹' {v}]).prod (uniformOn (Set.univ : Set (Fin N))) := by
  have hs : (fun ω : Ω × Fin N => V ω.1) ⁻¹' {v} =
      (V ⁻¹' {v}) ×ˢ Set.univ := by
    ext ω
    simp
  rw [hs, ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.prod_prod, measure_univ, mul_one,
    Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ]

omit [IsProbabilityMeasure μ] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSingletonClass Ω] in
/-- The terminal law conditioned at an earlier checkpoint is the smoothing
of that exact source fiber; it is not conditioning on the terminal time. -/
theorem smoothedTimeLaw_cond_checkpoint_map (v : A) :
    ((μ.prod (uniformOn (Set.univ : Set (Fin N))))[|(fun ω => V ω.1) ⁻¹' {v}]).map
      (fun ω => b ω.1 + ω.2.val) = smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N := by
  rw [independentOffset_cond_checkpoint]
  rfl

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The `a/N` bound under the actual positive-mass earlier checkpoint. -/
theorem smoothedTimeLaw_cond_checkpoint_event_bound (v : A)
    (hv : μ (V ⁻¹' {v}) ≠ 0) (E : Set ℕ) (a : ℕ) :
    |(smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N).real ((fun t => t + a) ⁻¹' E) -
      (smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N).real E| ≤ (a : ℝ) / N := by
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact smoothedTimeLaw_shift_event_bound (μ[|V ⁻¹' {v}]) b N E a

end Checkpoint

/-- The manuscript's `N >= T^10`, `a <= T` imply the exact `T^(-9)` error. -/
theorem terminal_shift_ratio_source_bound (a N : ℕ) (T : ℝ)
    (hT : 0 < T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    (a : ℝ) / N ≤ 1 / T ^ 9 := by
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (pow_pos hT 10) hN
  calc
    _ ≤ T / N := div_le_div_of_nonneg_right ha hNr.le
    _ ≤ T / T ^ 10 := div_le_div_of_nonneg_left hT.le (pow_pos hT 10) hN
    _ = 1 / T ^ 9 := by
      rw [show T ^ 10 = T ^ 9 * T by ring]
      field_simp

section SourceScale
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

theorem smoothedTimeLaw_source_event_bound (E : Set ℕ) (a : ℕ) (T : ℝ)
    (hT : 0 < T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |(smoothedTimeLaw μ b N).real ((fun t => t + a) ⁻¹' E) -
      (smoothedTimeLaw μ b N).real E| ≤ 1 / T ^ 9 :=
  (smoothedTimeLaw_shift_event_bound μ b N E a).trans
    (terminal_shift_ratio_source_bound a N T hT ha hN)

/-- The same scale bound applies directly to residues or any other observation. -/
theorem smoothedTimeLaw_source_observation_bound {G : Type*} [MeasurableSpace G]
    (F : ℕ → G) (E : Set G) (hE : MeasurableSet E) (a : ℕ) (T : ℝ)
    (hT : 0 < T) (ha : (a : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    |((smoothedTimeLaw μ b N).map (fun t => F (t + a))).real E -
      ((smoothedTimeLaw μ b N).map F).real E| ≤ 1 / T ^ 9 :=
  (smoothedTimeLaw_observation_shift_bound μ b N F E hE a).trans
    (terminal_shift_ratio_source_bound a N T hT ha hN)

end SourceScale

/-- A concrete positive offset length, with the required tenth-power budget. -/
noncomputable def terminalSmoothingLength (T : ℝ) : ℕ := max 1 ⌈T ^ 10⌉₊

theorem terminalSmoothingLength_pos (T : ℝ) : 0 < terminalSmoothingLength T := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem terminalSmoothingLength_ge (T : ℝ) : T ^ 10 ≤ (terminalSmoothingLength T : ℝ) := by
  unfold terminalSmoothingLength
  have hn : ⌈T ^ (10 : ℕ)⌉₊ ≤ max 1 ⌈T ^ (10 : ℕ)⌉₊ := Nat.le_max_right _ _
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

theorem terminalSmoothingLength_eq_ceil (T : ℝ) (hT : 0 < T) :
    terminalSmoothingLength T = ⌈T ^ 10⌉₊ := by
  have hc : (0 : ℝ) < (⌈T ^ (10 : ℕ)⌉₊ : ℝ) :=
    lt_of_lt_of_le (pow_pos hT 10) (Nat.le_ceil _)
  have hn : 0 < ⌈T ^ (10 : ℕ)⌉₊ := by exact_mod_cast hc
  exact max_eq_right (by omega)

/-- Source-scale smoothing with its length constructed, rather than postulated. -/
theorem smoothedTimeLaw_ceiling_source_bound {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
    (E : Set ℕ) (a : ℕ) (T : ℝ) (hT : 0 < T) (ha : (a : ℝ) ≤ T) :
    |(smoothedTimeLaw μ b (terminalSmoothingLength T)).real ((fun t => t + a) ⁻¹' E) -
      (smoothedTimeLaw μ b (terminalSmoothingLength T)).real E| ≤ 1 / T ^ 9 := by
  have : NeZero (terminalSmoothingLength T) := ⟨(terminalSmoothingLength_pos T).ne'⟩
  exact smoothedTimeLaw_source_event_bound μ b (terminalSmoothingLength T) E a T hT ha
    (terminalSmoothingLength_ge T)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.independentOffset_cond_checkpoint
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_cond_checkpoint_map
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_cond_checkpoint_event_bound
#print axioms BinaryFormMoat.EntropyIntegration.terminal_shift_ratio_source_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_source_event_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_source_observation_bound
#print axioms BinaryFormMoat.EntropyIntegration.terminalSmoothingLength_pos
#print axioms BinaryFormMoat.EntropyIntegration.terminalSmoothingLength_ge
#print axioms BinaryFormMoat.EntropyIntegration.terminalSmoothingLength_eq_ceil
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_ceiling_source_bound
