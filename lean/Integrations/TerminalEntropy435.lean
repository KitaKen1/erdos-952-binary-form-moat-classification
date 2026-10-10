import Integrations.FlagContinuity435
import Integrations.TerminalCoupling435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Source
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

omit [IsProbabilityMeasure μ] [NeZero N] [MeasurableSpace Bool]
  [MeasurableSingletonClass Bool] in
theorem smoothedTimeLaw_offset_identDistrib {G : Type*} [MeasurableSpace G] (F : ℕ → G) :
    IdentDistrib F (fun ω : Ω × Fin N => F (b ω.1 + ω.2.val))
      (smoothedTimeLaw μ b N) (terminalOffsetLaw μ N) := by
  refine ⟨(measurable_of_countable _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  exact Measure.map_map (measurable_of_countable _) (measurable_of_finite _)

omit [MeasurableSpace Bool] [MeasurableSingletonClass Bool] in
theorem smoothedTimeLaw_condEntropy_lift {S T : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (X : ℕ → S) (Z : ℕ → T) :
    condEntropy X Z (smoothedTimeLaw μ b N) =
      condEntropy (fun ω : Ω × Fin N => X (b ω.1 + ω.2.val))
        (fun ω => Z (b ω.1 + ω.2.val)) (terminalOffsetLaw μ N) :=
  (smoothedTimeLaw_offset_identDistrib μ b N (fun t => (X t, Z t))).condEntropy_eq
    (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_finite _) (measurable_of_finite _)

/-- Quantitative conditional entropy continuity for the actual smoothed
terminal law. Side-observation size is not charged. -/
theorem smoothedTimeLaw_condEntropy_shift_bound {S T : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (X : ℕ → S) (Z : ℕ → T) (a : ℕ) (ha : a ≤ N) :
    |condEntropy (fun t => X (t + a)) (fun t => Z (t + a)) (smoothedTimeLaw μ b N) -
      condEntropy X Z (smoothedTimeLaw μ b N)| ≤
      successEntropyCost ((a : ℝ) / N) + (a : ℝ) / N * Real.log (Fintype.card S) := by
  have hgood (ω : Ω × Fin N) (hω : terminalBoundaryFlag a ω = false) :
      b ω.1 + ω.2.val = windowBoundaryTime (b ω.1) N a ω.2.val := by
    apply (windowBoundaryTime_good _ _ _ _ ?_).symm
    simpa [terminalBoundaryFlag] using hω
  have h := condEntropy_flag_agreement_bound (terminalOffsetLaw μ N)
    (fun ω : Ω × Fin N => X (b ω.1 + ω.2.val))
    (fun ω => Z (b ω.1 + ω.2.val)) (terminalBoundaryFlag a)
    (fun ω => X (windowBoundaryTime (b ω.1) N a ω.2.val))
    (fun ω => Z (windowBoundaryTime (b ω.1) N a ω.2.val))
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
    (fun ω hω => ⟨congrArg X (hgood ω hω), congrArg Z (hgood ω hω)⟩)
  have he := ((terminalBoundaryTime_identDistrib μ b N a ha).comp
    (measurable_of_countable (fun t => (X t, Z t)))).condEntropy_eq
      (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)
  rw [he, terminalBoundaryFlag_mass μ N a ha] at h
  rw [smoothedTimeLaw_condEntropy_lift, smoothedTimeLaw_condEntropy_lift]
  simpa only [abs_sub_comm] using h

/-- Information-rate comparisons under the same terminal law pay twice the
target entropy continuity cost, with no auxiliary-alphabet logarithm. -/
theorem smoothedTimeLaw_condMutualInfo_shift_bound {S T U : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (X : ℕ → S) (Y : ℕ → T) (Z : ℕ → U) (a : ℕ) (ha : a ≤ N) :
    |condMutualInfo (fun t => X (t + a)) (fun t => Y (t + a)) (fun t => Z (t + a))
        (smoothedTimeLaw μ b N) - condMutualInfo X Y Z (smoothedTimeLaw μ b N)| ≤
      2 * (successEntropyCost ((a : ℝ) / N) +
        (a : ℝ) / N * Real.log (Fintype.card S)) := by
  have h₀ := smoothedTimeLaw_condEntropy_shift_bound μ b N X Z a ha
  have h₁ := smoothedTimeLaw_condEntropy_shift_bound μ b N X (fun t => (Y t, Z t)) a ha
  rw [condMutualInfo_eq' (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) _, condMutualInfo_eq' (measurable_of_countable _)
    (measurable_of_countable _) (measurable_of_countable _) _, abs_le]
  have hb₀ := abs_le.mp h₀
  have hb₁ := abs_le.mp h₁
  constructor <;> linarith [hb₀.1, hb₀.2, hb₁.1, hb₁.2]

/-- A length-L word over K letters incurs only its own L*log|K| cost. -/
theorem smoothedTimeLaw_word_condEntropy_shift_bound {K T : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (L : ℕ) (W : ℕ → (Fin L → K)) (Z : ℕ → T) (a : ℕ) (ha : a ≤ N) :
    |condEntropy (fun t => W (t + a)) (fun t => Z (t + a)) (smoothedTimeLaw μ b N) -
      condEntropy W Z (smoothedTimeLaw μ b N)| ≤
      successEntropyCost ((a : ℝ) / N) +
        (a : ℝ) / N * (L * Real.log (Fintype.card K)) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using
    smoothedTimeLaw_condEntropy_shift_bound μ b N W Z a ha

end Source
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_offset_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condEntropy_lift
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condEntropy_shift_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_condMutualInfo_shift_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_condEntropy_shift_bound
