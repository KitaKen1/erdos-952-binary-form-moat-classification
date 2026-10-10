import Integrations.DifferencePairEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Full finite histories retain the previous history, a representing pair,
and the fresh coin at each step. No infinite product probability space is used. -/
def PairedWalkSource (A : Type*) (N : ℕ → ℕ) : ℕ → Type _
  | 0 => A
  | n + 1 => DifferencePairSource (PairedWalkSource A N n) (N n) × Bool

instance pairedWalkSource_fintype {A : Type*} [Fintype A] (N : ℕ → ℕ) :
    (n : ℕ) → Fintype (PairedWalkSource A N n)
  | 0 => (inferInstance : Fintype A)
  | n + 1 => by
    change Fintype (DifferencePairSource (PairedWalkSource A N n) (N n) × Bool)
    letI := pairedWalkSource_fintype (A := A) N n
    infer_instance

instance pairedWalkSource_measurableSpace {A : Type*} [MeasurableSpace A] (N : ℕ → ℕ) :
    (n : ℕ) → MeasurableSpace (PairedWalkSource A N n)
  | 0 => (inferInstance : MeasurableSpace A)
  | n + 1 => by
    change MeasurableSpace (DifferencePairSource (PairedWalkSource A N n) (N n) × Bool)
    letI := pairedWalkSource_measurableSpace (A := A) N n
    infer_instance

instance pairedWalkSource_measurableSingletonClass {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] (N : ℕ → ℕ) :
    (n : ℕ) → MeasurableSingletonClass (PairedWalkSource A N n)
  | 0 => (inferInstance : MeasurableSingletonClass A)
  | n + 1 => by
    change MeasurableSingletonClass (DifferencePairSource (PairedWalkSource A N n) (N n) × Bool)
    let := pairedWalkSource_measurableSingletonClass (A := A) N n
    infer_instance

def pairedWalkOrigin {A : Type*} (N : ℕ → ℕ) : (n : ℕ) → PairedWalkSource A N n → A
  | 0 => id
  | n + 1 => fun ω => pairedWalkOrigin N n ω.1.1

def pairedWalkTime {A : Type*} (N : ℕ → ℕ) (b : A → ℕ) :
    (n : ℕ) → PairedWalkSource A N n → ℕ
  | 0 => b
  | n + 1 => fairEndpointTime (differencePairFirstTime (N n) (pairedWalkTime N b n))
      (differencePairSecondTime (N n) (pairedWalkTime N b n))

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

def pairedWalkLaw (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A) (b : A → ℕ) :
    (n : ℕ) → Measure (PairedWalkSource A N n)
  | 0 => μ
  | n + 1 => fairEndpointLaw (differencePairForwardLaw z (N n) (pairedWalkLaw z N μ b n)
      (pairedWalkTime N b n))

instance pairedWalkLaw_isProbabilityMeasure (z : ℕ → Point) (N : ℕ → ℕ)
    (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ) :
    (n : ℕ) → IsProbabilityMeasure (pairedWalkLaw z N μ b n)
  | 0 => (inferInstance : IsProbabilityMeasure μ)
  | n + 1 => by
    change IsProbabilityMeasure (fairEndpointLaw (differencePairForwardLaw z (N n)
      (pairedWalkLaw z N μ b n) (pairedWalkTime N b n)))
    let := pairedWalkLaw_isProbabilityMeasure z N μ b n
    infer_instance

variable (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

omit [IsProbabilityMeasure μ] in
theorem pairedWalkLaw_previous_map (n : ℕ) :
    (pairedWalkLaw z N μ b (n + 1)).map (fun ω => ω.1.1) = pairedWalkLaw z N μ b n := by
  change (fairEndpointLaw (differencePairForwardLaw z (N n) (pairedWalkLaw z N μ b n)
    (pairedWalkTime N b n))).map (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst, fairEndpointLaw,
    Measure.map_fst_prod, measure_univ, one_smul, differencePairForwardLaw_base_map]

omit [IsProbabilityMeasure μ] in
/-- The original base law is retained through every finite number of transitions. -/
theorem pairedWalkLaw_origin_map (n : ℕ) :
    (pairedWalkLaw z N μ b n).map (pairedWalkOrigin N n) = μ := by
  induction n with
  | zero => change μ.map id = μ; exact Measure.map_id
  | succ n ih =>
    change (pairedWalkLaw z N μ b (n + 1)).map
      (pairedWalkOrigin N n ∘ (fun ω => ω.1.1)) = μ
    rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
      pairedWalkLaw_previous_map, ih]

omit [IsProbabilityMeasure μ] in
theorem pairedWalkLaw_origin_checkpoint (n : ℕ) {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : A → B) (c : B) :
    pairedWalkLaw z N μ b n ((fun ω => V (pairedWalkOrigin N n ω)) ⁻¹' {c}) =
      μ (V ⁻¹' {c}) := by
  change pairedWalkLaw z N μ b n ((pairedWalkOrigin N n) ⁻¹' (V ⁻¹' {c})) = _
  rw [← Measure.map_apply (measurable_of_finite _) ((measurable_of_finite V)
    (MeasurableSet.singleton c)), pairedWalkLaw_origin_map]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pairedWalkTime_step_bounds (n : ℕ) (ω : PairedWalkSource A N (n + 1)) :
    pairedWalkTime N b n ω.1.1 ≤ pairedWalkTime N b (n + 1) ω ∧
      pairedWalkTime N b (n + 1) ω ≤ pairedWalkTime N b n ω.1.1 + N n := by
  apply fairEndpointTime_bounds (fun p => pairedWalkTime N b n p.1)
    (differencePairFirstTime (N n) (pairedWalkTime N b n))
    (differencePairSecondTime (N n) (pairedWalkTime N b n)) (N n)
  · intro ω
    exact (differencePairTimes_bounds (N n) (pairedWalkTime N b n) ω).1
  · intro ω
    exact (differencePairTimes_bounds (N n) (pairedWalkTime N b n) ω).2.1
  · intro ω
    exact (differencePairTimes_bounds (N n) (pairedWalkTime N b n) ω).2.2.1
  · intro ω
    exact (differencePairTimes_bounds (N n) (pairedWalkTime N b n) ω).2.2.2

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- One deterministic window budget holds for every history, not only almost surely. -/
theorem pairedWalkTime_total_bounds (n : ℕ) (ω : PairedWalkSource A N n) :
    b (pairedWalkOrigin N n ω) ≤ pairedWalkTime N b n ω ∧
      pairedWalkTime N b n ω ≤ b (pairedWalkOrigin N n ω) + ∑ j ∈ Finset.range n, N j := by
  induction n with
  | zero => simp [pairedWalkTime, pairedWalkOrigin]
  | succ n ih =>
    have h := pairedWalkTime_step_bounds N b n ω
    have hi := ih ω.1.1
    simp only [pairedWalkOrigin, Finset.sum_range_succ]
    omega

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pairedWalkPoint_step_eq (n : ℕ) :
    fairEndpointPoint (fun ω => z (differencePairFirstTime (N n) (pairedWalkTime N b n) ω))
      (fun ω => z (differencePairSecondTime (N n) (pairedWalkTime N b n) ω)) =
    (fun ω : PairedWalkSource A N (n + 1) => z (pairedWalkTime N b (n + 1) ω)) :=
  fairEndpointPoint_walk_eq z _ _

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.PairedWalkSource
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkSource_fintype
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkSource_measurableSpace
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkSource_measurableSingletonClass
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkOrigin
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTime
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_previous_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_origin_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_origin_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTime_step_bounds
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTime_total_bounds
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPoint_step_eq
