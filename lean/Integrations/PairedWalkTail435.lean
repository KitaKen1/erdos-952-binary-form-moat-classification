import Integrations.PairedWalkHistory435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Run the remaining ORIGINAL windows from any law on an intermediate history.
The law need not be a conditional law of the experiment that started at zero. -/
def pairedWalkTailLaw (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) :
    (r : ℕ) → Measure (PairedWalkSource A N (k + r))
  | 0 => ν
  | r + 1 => fairEndpointLaw (differencePairForwardLaw z (N (k + r))
      (pairedWalkTailLaw z N b k ν r) (pairedWalkTime N b (k + r)))

instance pairedWalkTailLaw_isProbabilityMeasure (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν] :
    (r : ℕ) → IsProbabilityMeasure (pairedWalkTailLaw z N b k ν r)
  | 0 => (inferInstance : IsProbabilityMeasure ν)
  | r + 1 => by
    change IsProbabilityMeasure (fairEndpointLaw (differencePairForwardLaw z (N (k + r))
      (pairedWalkTailLaw z N b k ν r) (pairedWalkTime N b (k + r))))
    let := pairedWalkTailLaw_isProbabilityMeasure z N b k ν r
    infer_instance

omit [MeasurableSingletonClass A] in
theorem pairedWalkTailLaw_original (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A)
    (b : A → ℕ) (k r : ℕ) :
    pairedWalkTailLaw z N b k (pairedWalkLaw z N μ b k) r = pairedWalkLaw z N μ b (k + r) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pairedWalkTailLaw, ih]; rfl

theorem pairedWalkTailLaw_previous_map (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (r : ℕ) :
    (pairedWalkTailLaw z N b k ν (r + 1)).map (fun ω => ω.1.1) =
      pairedWalkTailLaw z N b k ν r := by
  change (fairEndpointLaw (differencePairForwardLaw z (N (k + r))
    (pairedWalkTailLaw z N b k ν r) (pairedWalkTime N b (k + r)))).map
    (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst, fairEndpointLaw,
    Measure.map_fst_prod, measure_univ, one_smul, differencePairForwardLaw_base_map]

theorem pairedWalkTailLaw_past_map (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (r : ℕ) :
    (pairedWalkTailLaw z N b k ν r).map (pairedWalkPast N k r) = ν := by
  induction r with
  | zero => exact Measure.map_id
  | succ r ih =>
    change (pairedWalkTailLaw z N b k ν (r + 1)).map
      (pairedWalkPast N k r ∘ (fun ω => ω.1.1)) = _
    rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
      pairedWalkTailLaw_previous_map, ih]

theorem pairedWalkTailLaw_checkpoint_mass (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (r : ℕ)
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N k → B) (c : B) :
    pairedWalkTailLaw z N b k ν r ((fun ω => V (pairedWalkPast N k r ω)) ⁻¹' {c}) =
      ν (V ⁻¹' {c}) := by
  change pairedWalkTailLaw z N b k ν r ((pairedWalkPast N k r) ⁻¹' (V ⁻¹' {c})) = _
  rw [← Measure.map_apply (measurable_of_finite _) ((measurable_of_finite V)
    (MeasurableSet.singleton c)), pairedWalkTailLaw_past_map]

/-- Every earlier checkpoint commutes with the complete remaining experiment.
Zero fibers are included as equality of measures; no probability instance for
a zero conditional measure is assumed. -/
theorem pairedWalkTailLaw_cond_checkpoint (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν] (r : ℕ)
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N k → B) (c : B) :
    (pairedWalkTailLaw z N b k ν r)[|(fun ω => V (pairedWalkPast N k r ω)) ⁻¹' {c}] =
      pairedWalkTailLaw z N b k (ν[|V ⁻¹' {c}]) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (fairEndpointLaw (differencePairForwardLaw z (N (k + r))
      (pairedWalkTailLaw z N b k ν r) (pairedWalkTime N b (k + r))))[|
      (fun ω => V (pairedWalkPast N k r ω.1.1)) ⁻¹' {c}] = _
    rw [differencePairFairLaw_cond_checkpoint z (N (k + r))
      (pairedWalkTailLaw z N b k ν r) (pairedWalkTime N b (k + r))
      (fun ω => V (pairedWalkPast N k r ω)) c, ih]
    rfl

/-- On positive original checkpoint fibers, this tail is the original conditional
future. The equality itself also holds for zero fibers. -/
theorem pairedWalkLaw_cond_past (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A)
    [IsProbabilityMeasure μ] (b : A → ℕ) (k r : ℕ)
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N k → B) (c : B) :
    (pairedWalkLaw z N μ b (k + r))[|(fun ω => V (pairedWalkPast N k r ω)) ⁻¹' {c}] =
      pairedWalkTailLaw z N b k ((pairedWalkLaw z N μ b k)[|V ⁻¹' {c}]) r := by
  rw [← pairedWalkTailLaw_original z N μ b k r]
  exact pairedWalkTailLaw_cond_checkpoint z N b k (pairedWalkLaw z N μ b k) r V c

/-- A deterministic retained history representing ANY exact starting time.
It is used to define a fresh experiment, even when the original law assigns
that time probability zero. Its old representing pairs need not have positive mass. -/
def pairedWalkZeroHistory (N : ℕ → ℕ) (a : A) : (k : ℕ) → PairedWalkSource A N k
  | 0 => a
  | k + 1 => ((pairedWalkZeroHistory N a k, fun _ => (0, 0)), false)

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pairedWalkTime_zeroHistory (N : ℕ → ℕ) (b : A → ℕ) (a : A) (k : ℕ) :
    pairedWalkTime N b k (pairedWalkZeroHistory N a k) = b a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [pairedWalkZeroHistory, pairedWalkTime, fairEndpointTime, Bool.false_eq_true,
      ite_false, differencePairSecondTime, Fin.val_zero, Nat.add_zero] using ih

theorem pairedWalkTailLaw_exact_start_time (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (a : A) (k : ℕ) :
    (pairedWalkTailLaw z N b k (Measure.dirac (pairedWalkZeroHistory N a k)) 0).map
      (pairedWalkTime N b k) = Measure.dirac (b a) := by
  rw [pairedWalkTailLaw, Measure.map_dirac' (measurable_of_finite _), pairedWalkTime_zeroHistory]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pairedWalkCheckpoint_previous (N : ℕ → ℕ) (n j : ℕ) (hj : j ≤ n) :
    pairedWalkCheckpoint (A := A) N (n + 1) ⟨j, by omega⟩ =
      pairedWalkCheckpoint N n ⟨j, by omega⟩ ∘ (fun ω => ω.1.1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h : pairedWalkCheckpoint (A := A) N (j + r + 1) ⟨j, by omega⟩ =
      pairedWalkPast N j (r + 1) := pairedWalkCheckpoint_add N j (r + 1) (by omega)
  rw [h, pairedWalkCheckpoint_add N j r]
  rfl

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pairedWalkCheckpoint_self (N : ℕ → ℕ) (n : ℕ) :
    pairedWalkCheckpoint (A := A) N n ⟨n, by omega⟩ = id :=
  pairedWalkCheckpoint_add N n 0 (by omega)

/-- Every intermediate marginal of a restarted experiment has its exact tail
law, on the same full history source. -/
theorem pairedWalkTailLaw_checkpoint_map (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (r j : ℕ) (hj : j ≤ r) :
    (pairedWalkTailLaw z N b k ν r).map
      (pairedWalkCheckpoint N (k + r) ⟨k + j, by omega⟩) = pairedWalkTailLaw z N b k ν j := by
  induction r generalizing j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rw [pairedWalkCheckpoint_self, Measure.map_id]
  | succ r ih =>
    by_cases he : j = r + 1
    · subst j
      rw [pairedWalkCheckpoint_self, Measure.map_id]
    · have hjr : j ≤ r := by omega
      have hp : pairedWalkCheckpoint (A := A) N (k + (r + 1)) ⟨k + j, by omega⟩ =
          pairedWalkCheckpoint N (k + r) ⟨k + j, by omega⟩ ∘ (fun ω => ω.1.1) :=
        pairedWalkCheckpoint_previous N (k + r) (k + j) (by omega)
      rw [hp,
        ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
        pairedWalkTailLaw_previous_map]
      exact ih j hjr

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_original
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_previous_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_past_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_checkpoint_mass
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_cond_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkLaw_cond_past
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkZeroHistory
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTime_zeroHistory
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_exact_start_time
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_previous
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_self
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_checkpoint_map
