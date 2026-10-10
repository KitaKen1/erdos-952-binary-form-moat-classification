import Integrations.TerminalSchedule435
import Mathlib.Probability.IdentDistrib

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Replace just the first `a` offsets by the upper boundary of the shifted
window. The remaining offsets give literally the same terminal time. -/
def windowBoundaryTime (b N a i : ℕ) : ℕ :=
  if i < a then b + N + i else b + i

def terminalBoundaryFlag {Ω : Type*} (a : ℕ) (ω : Ω × Fin N) : Bool :=
  decide (ω.2.val < a)

theorem windowBoundaryTime_good (b N a i : ℕ) (hi : ¬i < a) :
    windowBoundaryTime b N a i = b + i := by
  simp [windowBoundaryTime, hi]

/-- Boundary replacement has exactly the shifted window's multiset of
times. Finite-sum cancellation avoids a cyclic-permutation construction. -/
theorem windowBoundary_sum (f : ℕ → ℝ) (b N a : ℕ) (ha : a ≤ N) :
    (∑ i ∈ Finset.range N, f (windowBoundaryTime b N a i)) =
      ∑ i ∈ Finset.range N, f (b + i + a) := by
  have hnew := Finset.sum_range_add (fun i => f (windowBoundaryTime b N a i)) a (N - a)
  have hold := Finset.sum_range_add (fun i => f (b + i)) a (N - a)
  rw [Nat.add_sub_of_le ha] at hnew hold
  have hhead : (∑ i ∈ Finset.range a, f (windowBoundaryTime b N a i)) =
      ∑ i ∈ Finset.range a, f (b + N + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [windowBoundaryTime, Finset.mem_range.mp hi]
  have htail : ∀ i, f (windowBoundaryTime b N a (a + i)) = f (b + (a + i)) := by
    intro i
    rw [windowBoundaryTime_good _ _ _ _ (by omega)]
  rw [hhead] at hnew
  simp_rw [htail] at hnew
  have hshift := window_sum_shift_identity f b N a
  linarith

theorem window_prefix_count (N a : ℕ) (ha : a ≤ N) :
    (∑ i ∈ Finset.range N, if i < a then (1 : ℝ) else 0) = a := by
  have hs := Finset.sum_range_add (fun i => if i < a then (1 : ℝ) else 0) a (N - a)
  rw [Nat.add_sub_of_le ha] at hs
  have hhead : (∑ i ∈ Finset.range a, if i < a then (1 : ℝ) else 0) = a := by
    calc
      _ = ∑ _i ∈ Finset.range a, (1 : ℝ) :=
        Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi))
      _ = a := by simp
  have htail : ∀ i, (if a + i < a then (1 : ℝ) else 0) = 0 := fun i => ite_eq_right (by omega)
  rw [hhead] at hs
  simp_rw [htail] at hs
  simpa using hs

section Source
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

noncomputable def terminalOffsetLaw : Measure (Ω × Fin N) :=
  μ.prod (uniformOn (Set.univ : Set (Fin N)))

instance terminalOffsetLaw_isProbabilityMeasure : IsProbabilityMeasure (terminalOffsetLaw μ N) := by
  unfold terminalOffsetLaw
  infer_instance

omit [NeZero N] in
/-- Exact expectation for any observable on the finite offset experiment. -/
theorem terminalOffsetLaw_integral (F : Ω × Fin N → ℝ) :
    ∫ ω, F ω ∂terminalOffsetLaw μ N =
      ∫ ω, (∑ j : Fin N, F (ω, j)) / N ∂μ := by
  classical
  rw [terminalOffsetLaw, integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [integral_fintype Integrable.of_finite]
  have hs (j : Fin N) : (uniformOn (Set.univ : Set (Fin N))).real {j} = 1 / (N : ℝ) := by
    simp [measureReal_def, uniformOn_univ]
  simp_rw [hs, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

omit [NeZero N] in
theorem terminalBoundaryFlag_mass (a : ℕ) (ha : a ≤ N) :
    (terminalOffsetLaw μ N).real (terminalBoundaryFlag (Ω := Ω) a ⁻¹' {true}) =
      (a : ℝ) / N := by
  classical
  rw [← integral_indicator_one (Set.toFinite _).measurableSet,
    terminalOffsetLaw_integral]
  have hsum (ω : Ω) : (∑ j : Fin N,
      (terminalBoundaryFlag a ⁻¹' {true}).indicator (1 : Ω × Fin N → ℝ) (ω, j)) = a := by
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
      terminalBoundaryFlag, decide_eq_true_eq, Pi.one_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < a then (1 : ℝ) else 0)]
    exact window_prefix_count N a ha
  simp_rw [hsum]
  simp

/-- The replacement and actual shifted times have identical laws under
the original offset experiment, not an assumed common marginal. -/
theorem terminalBoundaryTime_identDistrib (a : ℕ) (ha : a ≤ N) :
    IdentDistrib (fun ω : Ω × Fin N => windowBoundaryTime (b ω.1) N a ω.2.val)
      (fun ω => b ω.1 + ω.2.val + a) (terminalOffsetLaw μ N) (terminalOffsetLaw μ N) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  ext E hE
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((terminalOffsetLaw μ N).map _).real E = ((terminalOffsetLaw μ N).map _).real E
  rw [← integral_indicator_one hE, ← integral_indicator_one hE,
    integral_map (measurable_of_finite _).aemeasurable
      ((measurable_of_countable _).aestronglyMeasurable),
    integral_map (measurable_of_finite _).aemeasurable
      ((measurable_of_countable _).aestronglyMeasurable),
    terminalOffsetLaw_integral, terminalOffsetLaw_integral]
  apply integral_congr_ae
  filter_upwards [] with ω
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => E.indicator 1 (windowBoundaryTime (b ω) N a i)),
    Fin.sum_univ_eq_sum_range (fun i => E.indicator 1 (b ω + i + a))]
  exact windowBoundary_sum (E.indicator 1) (b ω) N a ha

end Source
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.windowBoundaryTime_good
#print axioms BinaryFormMoat.EntropyIntegration.windowBoundary_sum
#print axioms BinaryFormMoat.EntropyIntegration.window_prefix_count
#print axioms BinaryFormMoat.EntropyIntegration.terminalOffsetLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.terminalOffsetLaw_integral
#print axioms BinaryFormMoat.EntropyIntegration.terminalBoundaryFlag_mass
#print axioms BinaryFormMoat.EntropyIntegration.terminalBoundaryTime_identDistrib
