import Integrations.WindowSmoothing435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section FiniteSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

/-- An independent uniform terminal offset, added to the original base time. -/
noncomputable def smoothedTimeLaw : Measure ℕ :=
  (μ.prod (uniformOn (Set.univ : Set (Fin N)))).map (fun ω => b ω.1 + ω.2.val)

instance smoothedTimeLaw_isProbabilityMeasure : IsProbabilityMeasure (smoothedTimeLaw μ b N) := by
  unfold smoothedTimeLaw
  infer_instance

omit [NeZero N] in
/-- Exact mixture formula; the base time is allowed to have any finite law. -/
theorem smoothedTimeLaw_integral (f : ℕ → ℝ) :
    ∫ t, f t ∂smoothedTimeLaw μ b N = ∫ ω, windowAverage f (b ω) N ∂μ := by
  classical
  rw [smoothedTimeLaw, integral_map (measurable_of_finite _).aemeasurable
    ((measurable_of_countable f).aestronglyMeasurable),
    integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [integral_fintype Integrable.of_finite]
  have hs (j : Fin N) : (uniformOn (Set.univ : Set (Fin N))).real {j} = 1 / (N : ℝ) := by
    simp [measureReal_def, uniformOn_univ]
  simp_rw [hs, smul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => f (b ω + i))]
  simp [windowAverage, div_eq_mul_inv, mul_comm]

/-- Uniform smoothing controls every bounded test function, including indicators. -/
theorem smoothedTimeLaw_shift_test_bound (f : ℕ → ℝ)
    (h₀ : ∀ i, 0 ≤ f i) (h₁ : ∀ i, f i ≤ 1) (a : ℕ) :
    |(∫ t, f (t + a) ∂smoothedTimeLaw μ b N) -
      (∫ t, f t ∂smoothedTimeLaw μ b N)| ≤ (a : ℝ) / N := by
  rw [smoothedTimeLaw_integral, smoothedTimeLaw_integral,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  calc
    _ ≤ ∫ ω, |windowAverage (fun t => f (t + a)) (b ω) N -
        windowAverage f (b ω) N| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ω, (a : ℝ) / N ∂μ := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro ω
      change |windowAverage (fun t => f (t + a)) (b ω) N -
        windowAverage f (b ω) N| ≤ (a : ℝ) / N
      have heq : windowAverage (fun t => f (t + a)) (b ω) N =
          windowAverage f (b ω + a) N := by
        unfold windowAverage
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        change f (b ω + i + a) = f (b ω + a + i)
        congr 1
        omega
      rw [heq]
      exact windowAverage_shift_bound f h₀ h₁ (b ω) N a (NeZero.pos N)
    _ = (a : ℝ) / N := by simp

/-- Every event has probability error at most `a/N`; hence this is also a
total-variation bound, without introducing signed-measure machinery. -/
theorem smoothedTimeLaw_shift_event_bound (E : Set ℕ) (a : ℕ) :
    |(smoothedTimeLaw μ b N).real ((fun t => t + a) ⁻¹' E) -
      (smoothedTimeLaw μ b N).real E| ≤ (a : ℝ) / N := by
  classical
  have h := smoothedTimeLaw_shift_test_bound μ b N (E.indicator 1)
    (fun i => by by_cases hi : i ∈ E <;> simp [hi])
    (fun i => by by_cases hi : i ∈ E <;> simp [hi]) a
  have hi : (fun t => E.indicator (1 : ℕ → ℝ) (t + a)) =
      ((fun t => t + a) ⁻¹' E).indicator 1 := by
    ext t
    simp [Set.indicator_apply]
  rw [hi, integral_indicator_one (Set.to_countable _).measurableSet,
    integral_indicator_one (Set.to_countable _).measurableSet] at h
  exact h

/-- Deterministic observations of time preserve the event error bound. -/
theorem smoothedTimeLaw_observation_shift_bound {T : Type*} [MeasurableSpace T]
    (F : ℕ → T) (E : Set T) (hE : MeasurableSet E) (a : ℕ) :
    |((smoothedTimeLaw μ b N).map (fun t => F (t + a))).real E -
      ((smoothedTimeLaw μ b N).map F).real E| ≤ (a : ℝ) / N := by
  rw [map_measureReal_apply (measurable_of_countable _) hE,
    map_measureReal_apply (measurable_of_countable _) hE]
  exact smoothedTimeLaw_shift_event_bound μ b N (F ⁻¹' E) a

end FiniteSource
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_integral
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_shift_test_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_shift_event_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_observation_shift_bound
