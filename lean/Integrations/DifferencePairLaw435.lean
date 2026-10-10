import Integrations.DifferenceForwardLaw435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

abbrev DifferencePairSource (A : Type*) (N : ℕ) :=
  A × (Unit → (Fin (N + 1) × Fin (N + 1)))

/-- Uniform DISTINCT differences are pushed to their deterministic representing
pairs. The time pairs themselves are not sampled uniformly. -/
def differencePairOffsetLaw (z : ℕ → Point) (N t : ℕ) :
    Measure (Fin (N + 1) × Fin (N + 1)) :=
  (uniformOn (Set.univ : Set (WalkDifferences (fun k => z (t + k)) N))).map
    (walkDifferenceTimes (fun k => z (t + k)) N)

instance differencePairOffsetLaw_isProbabilityMeasure (z : ℕ → Point) (N t : ℕ) :
    IsProbabilityMeasure (differencePairOffsetLaw z N t) := by
  unfold differencePairOffsetLaw
  infer_instance

section Forward
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

def differencePairForwardLaw : Measure (DifferencePairSource A N) :=
  continuationResamplingLaw (J := Unit) μ (fun a => differencePairOffsetLaw z N (b a))

instance differencePairForwardLaw_isProbabilityMeasure :
    IsProbabilityMeasure (differencePairForwardLaw z N μ b) := by
  unfold differencePairForwardLaw
  infer_instance

def differencePairFirstTime (ω : DifferencePairSource A N) : ℕ :=
  b ω.1 + (ω.2 ()).1.val

def differencePairSecondTime (ω : DifferencePairSource A N) : ℕ :=
  b ω.1 + (ω.2 ()).2.val

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem differencePairTimes_bounds (ω : DifferencePairSource A N) :
    b ω.1 ≤ differencePairFirstTime N b ω ∧ differencePairFirstTime N b ω ≤ b ω.1 + N ∧
    b ω.1 ≤ differencePairSecondTime N b ω ∧ differencePairSecondTime N b ω ≤ b ω.1 + N := by
  have h1 := (ω.2 ()).1.isLt
  have h2 := (ω.2 ()).2.isLt
  unfold differencePairFirstTime differencePairSecondTime
  omega

omit [IsProbabilityMeasure μ] in
theorem differencePairForwardLaw_base_map :
    (differencePairForwardLaw z N μ b).map Prod.fst = μ := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton a)]
  exact continuationResamplingLaw_fiber μ (fun a => differencePairOffsetLaw z N (b a)) a

omit [IsProbabilityMeasure μ] in
theorem differencePairForwardLaw_real_base_fiber (a : A) :
    (differencePairForwardLaw z N μ b).real (Prod.fst ⁻¹' {a}) = μ.real {a} := by
  rw [← map_measureReal_apply measurable_fst (MeasurableSet.singleton a),
    differencePairForwardLaw_base_map]

theorem differencePairForwardLaw_cond_pair_map (a : A) (ha : μ {a} ≠ 0) :
    ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]).map (fun ω => ω.2 ()) =
      differencePairOffsetLaw z N (b a) :=
  continuationResamplingLaw_cond_trial_map μ (fun a => differencePairOffsetLaw z N (b a)) a ha ()

omit [IsProbabilityMeasure μ] in
theorem differencePairForwardLaw_cond_zero_fiber (a : A) (ha : μ {a} = 0) :
    (differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}] = 0 :=
  continuationResamplingLaw_cond_zero_fiber μ (fun a => differencePairOffsetLaw z N (b a)) a ha

/-- Exact endpoint-pair distribution on a positive BASE fiber. -/
theorem differencePairForwardLaw_cond_endpoint_map (a : A) (ha : μ {a} ≠ 0) :
    ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]).map
      (fun ω => (z (differencePairFirstTime N b ω), z (differencePairSecondTime N b ω))) =
    (uniformOn (Set.univ : Set (WalkDifferences (fun k => z (b a + k)) N))).map
      (fun h => (z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).1.val),
        z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).2.val))) := by
  rw [show (differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}] =
      (Measure.pi (fun _ : Unit => differencePairOffsetLaw z N (b a))).map (Prod.mk a) from
        continuationResamplingLaw_cond_fiber μ (fun a => differencePairOffsetLaw z N (b a)) a ha,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  let f : Fin (N + 1) × Fin (N + 1) → Point × Point :=
    fun p => (z (b a + p.1.val), z (b a + p.2.val))
  change (Measure.pi (fun _ : Unit => differencePairOffsetLaw z N (b a))).map
    (f ∘ Function.eval ()) = _
  rw [← Measure.map_map (measurable_of_finite f) (measurable_pi_apply ()),
    (measurePreserving_eval (fun _ : Unit => differencePairOffsetLaw z N (b a)) ()).map_eq,
    differencePairOffsetLaw, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

omit [IsProbabilityMeasure μ] in
/-- Earlier checkpoints are functions of the retained original base. Conditioning
commutes with the paired transition, including zero-mass checkpoints. -/
theorem differencePairForwardLaw_cond_checkpoint {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : A → B) (c : B) :
    (differencePairForwardLaw z N μ b)[|(fun ω => V ω.1) ⁻¹' {c}] =
      differencePairForwardLaw z N (μ[|V ⁻¹' {c}]) b := by
  classical
  have hV : MeasurableSet (V ⁻¹' {c}) := (measurable_of_finite V) (MeasurableSet.singleton c)
  have hC : MeasurableSet ((fun ω : DifferencePairSource A N => V ω.1) ⁻¹' {c}) :=
    (measurable_of_finite _) (MeasurableSet.singleton c)
  have hm : differencePairForwardLaw z N μ b ((fun ω => V ω.1) ⁻¹' {c}) = μ (V ⁻¹' {c}) := by
    change differencePairForwardLaw z N μ b (Prod.fst ⁻¹' (V ⁻¹' {c})) = _
    rw [← Measure.map_apply measurable_fst hV, differencePairForwardLaw_base_map]
  ext E hE
  rw [cond_apply hC, hm]
  simp only [differencePairForwardLaw, continuationResamplingLaw_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [cond_apply hV]
  by_cases ha : V a = c
  · have h1 : (Prod.mk a) ⁻¹' (((fun ω : DifferencePairSource A N => V ω.1) ⁻¹' {c}) ∩ E) =
        (Prod.mk a) ⁻¹' E := by ext v; simp [ha]
    have h2 : V ⁻¹' {c} ∩ {a} = ({a} : Set A) := by ext v; simp [ha]
    simp only [h1, h2, mul_assoc]
  · have h1 : (Prod.mk a) ⁻¹' (((fun ω : DifferencePairSource A N => V ω.1) ⁻¹' {c}) ∩ E) = ∅ := by
      ext v; simp [ha]
    have h2 : V ⁻¹' {c} ∩ {a} = (∅ : Set A) := by ext v; simp [ha]
    simp [h1, h2]

end Forward
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.DifferencePairSource
#print axioms BinaryFormMoat.GeometryIntegration.differencePairOffsetLaw
#print axioms BinaryFormMoat.GeometryIntegration.differencePairOffsetLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.differencePairFirstTime
#print axioms BinaryFormMoat.GeometryIntegration.differencePairSecondTime
#print axioms BinaryFormMoat.GeometryIntegration.differencePairTimes_bounds
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_base_map
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_real_base_fiber
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_pair_map
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_zero_fiber
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_endpoint_map
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_checkpoint
