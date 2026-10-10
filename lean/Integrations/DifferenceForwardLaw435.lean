import Integrations.DifferenceEndpoint435
import Integrations.ContinuationResampling435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A common finite offset type allows windows with different difference sets
to be mixed without replacing uniform differences by uniform endpoint pairs. -/
def differenceOffsetLaw (z : ℕ → Point) (N t : ℕ) : Measure (Fin (N + 1)) :=
  (differenceEndpointSourceLaw (fun k => z (t + k)) N).map
    (differenceEndpointIndex (fun k => z (t + k)) N)

instance differenceOffsetLaw_isProbabilityMeasure (z : ℕ → Point) (N t : ℕ) :
    IsProbabilityMeasure (differenceOffsetLaw z N t) := by
  unfold differenceOffsetLaw
  infer_instance

theorem differenceOffsetLaw_integral (z : ℕ → Point) (N t : ℕ) (f : Point → ℝ) :
    ∫ i, f (z (t + i.val)) ∂differenceOffsetLaw z N t =
      ((∫ h : WalkDifferences (fun k => z (t + k)) N,
        f (z (t + (walkDifferenceTimes (fun k => z (t + k)) N h).1.val))
        ∂uniformOn (Set.univ : Set (WalkDifferences (fun k => z (t + k)) N))) +
       (∫ h : WalkDifferences (fun k => z (t + k)) N,
        f (z (t + (walkDifferenceTimes (fun k => z (t + k)) N h).2.val))
        ∂uniformOn (Set.univ : Set (WalkDifferences (fun k => z (t + k)) N)))) / 2 := by
  rw [differenceOffsetLaw, integral_map (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable]
  exact differenceEndpointSourceLaw_integral (fun k => z (t + k)) N f

section Forward
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

/-- First retain the original base value; on its exact fiber sample the
uniform-difference/fair-endpoint transition for that base time. Unit is the
one-trial index of the already checked posterior sampling construction. -/
def differenceForwardLaw : Measure (A × (Unit → Fin (N + 1))) :=
  continuationResamplingLaw (J := Unit) μ (fun a => differenceOffsetLaw z N (b a))

instance differenceForwardLaw_isProbabilityMeasure :
    IsProbabilityMeasure (differenceForwardLaw z N μ b) := by
  unfold differenceForwardLaw
  infer_instance

def differenceForwardTime (ω : A × (Unit → Fin (N + 1))) : ℕ :=
  b ω.1 + (ω.2 ()).val

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem differenceForwardTime_bounds (ω : A × (Unit → Fin (N + 1))) :
    b ω.1 ≤ differenceForwardTime N b ω ∧
      differenceForwardTime N b ω ≤ b ω.1 + N := by
  have h := (ω.2 ()).isLt
  unfold differenceForwardTime
  omega

omit [IsProbabilityMeasure μ] in
theorem differenceForwardLaw_base_map :
    (differenceForwardLaw z N μ b).map Prod.fst = μ := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
  exact continuationResamplingLaw_fiber μ (fun a => differenceOffsetLaw z N (b a)) a

theorem differenceForwardLaw_cond_offset_map (a : A) (ha : μ {a} ≠ 0) :
    ((differenceForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]).map
      (fun ω => ω.2 ()) = differenceOffsetLaw z N (b a) :=
  continuationResamplingLaw_cond_trial_map μ (fun a => differenceOffsetLaw z N (b a)) a ha ()

omit [IsProbabilityMeasure μ] in
theorem differenceForwardLaw_cond_zero_fiber (a : A) (ha : μ {a} = 0) :
    (differenceForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}] = 0 :=
  continuationResamplingLaw_cond_zero_fiber μ (fun a => differenceOffsetLaw z N (b a)) a ha

section Roots
variable {J : Type*} [MeasurableSpace J] (ξ : Measure J) [IsProbabilityMeasure ξ]

/-- Root choices are sampled separately from the whole base/endpoint law.
The construction does not infer independence after conditioning on residues. -/
def rootDifferenceForwardLaw : Measure (J × (A × (Unit → Fin (N + 1)))) :=
  ξ.prod (differenceForwardLaw z N μ b)

omit [IsProbabilityMeasure ξ] in
theorem rootDifferenceForwardLaw_root_map :
    (rootDifferenceForwardLaw z N μ b ξ).map Prod.fst = ξ := by
  rw [rootDifferenceForwardLaw, Measure.map_fst_prod, measure_univ, one_smul]

omit [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
theorem rootDifferenceForwardLaw_forward_map :
    (rootDifferenceForwardLaw z N μ b ξ).map Prod.snd = differenceForwardLaw z N μ b := by
  rw [rootDifferenceForwardLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem rootDifferenceForwardLaw_independent_time :
    IndepFun (Prod.fst : J × (A × (Unit → Fin (N + 1))) → J)
      (fun ω => differenceForwardTime N b ω.2) (rootDifferenceForwardLaw z N μ b ξ) :=
  indepFun_prod measurable_id (measurable_of_finite _)

end Roots
end Forward
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.differenceOffsetLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.differenceOffsetLaw_integral
#print axioms BinaryFormMoat.GeometryIntegration.differenceForwardLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.differenceForwardTime_bounds
#print axioms BinaryFormMoat.GeometryIntegration.differenceForwardLaw_base_map
#print axioms BinaryFormMoat.GeometryIntegration.differenceForwardLaw_cond_offset_map
#print axioms BinaryFormMoat.GeometryIntegration.differenceForwardLaw_cond_zero_fiber
#print axioms BinaryFormMoat.GeometryIntegration.rootDifferenceForwardLaw_root_map
#print axioms BinaryFormMoat.GeometryIntegration.rootDifferenceForwardLaw_forward_map
#print axioms BinaryFormMoat.GeometryIntegration.rootDifferenceForwardLaw_independent_time
