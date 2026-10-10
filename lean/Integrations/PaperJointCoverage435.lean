import Integrations.PaperInformationThresholds435
import Integrations.PaperJointBatchEntropy435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The SAME joint batch that supplies top entropy also supplies all actual
backward coverage, for arbitrary earlier laws. No second prime set is chosen. -/
theorem PaperJointBatch.coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 c a0 : ℝ) (l T : ℕ) (hT : 2 ≤ T) (bad P : Finset ℕ)
    [∀ p : P, NeZero p.val] (batch : PaperJointBatch f R M m g0 c a0 l T bad P)
    (inputs : PaperInformationThresholds f.natDegree R M (by omega) g0)
    (hloglo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (e : ∀ p : P, Q ≃ primeRootSet f p.val) (z : ℕ → Point) (a : A → ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    ∀ i ≤ paperCheckpointStop f.natDegree M (T : ℝ) (by have := inputs.two; omega),
      ∀ k : ℕ, ∀ ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k),
        IsProbabilityMeasure ν →
        k ≤ paperMiddleStartPosition f M R m g0 T i P (batch.middle i) →
        paperFullTailDeficientFraction P (primeRootSet f) e z f.natDegree M g0 a k ν i ≤
          paperCoverageEta i := by
  exact paperMiddleBottomCertificates_backward_coverage f hf hd M R m hm g0 T
    inputs.two inputs.accuracy inputs.base inputs.margins inputs.tail inputs.shared inputs.future
    P (fun p hp => (batch.primes p hp).1) (primeRootSet f)
    (fun p hp => (batch.primes p hp).2.2.2)
    (fun p hp ρ hρ => (mem_primeRootSet f p (batch.primes p hp).1 ρ).mp hρ) e
    hT batch.nonempty (fun p hp => (batch.primes p hp).2.1)
    (fun p hp => (batch.primes p hp).2.2.1) hloglo hloghi batch.middle batch.bottom z a hstep hinj

/-- Initial-source coverage on the SAME full-terminal experiment as the
joint batch's terminal and middle-start entropy. -/
theorem PaperJointBatch.initial_coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 c a0 : ℝ) (l T : ℕ) (hT : 2 ≤ T) (bad P : Finset ℕ)
    [∀ p : P, NeZero p.val] (batch : PaperJointBatch f R M m g0 c a0 l T bad P)
    (inputs : PaperInformationThresholds f.natDegree R M (by omega) g0)
    (hloglo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (e : ∀ p : P, Q ≃ primeRootSet f p.val) (z : ℕ → Point) (a : A → ℕ)
    (ν : Measure A) (hν : IsProbabilityMeasure ν)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (i : ℕ) (hi : i ≤ paperCheckpointStop f.natDegree M (T : ℝ) (by have := inputs.two; omega)) :
    paperFullTailDeficientFraction P (primeRootSet f) e z f.natDegree M g0 a 0 ν i ≤ paperCoverageEta i :=
  PaperJointBatch.coverage f hf hd R M m hm g0 c a0 l T hT bad P batch inputs hloglo hloghi
    e z a hstep hinj i hi 0 ν hν (Nat.zero_le _)

/-- Coverage at EVERY positive ORIGINAL exact middle-start fiber. The
conditional restart and its probability instance are derived; no conditional
coverage premise is supplied. Zero fibers are intentionally not normalized. -/
theorem PaperJointBatch.conditional_coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 c a0 : ℝ) (l T : ℕ) (hT : 2 ≤ T) (bad P : Finset ℕ)
    [∀ p : P, NeZero p.val] (batch : PaperJointBatch f R M m g0 c a0 l T bad P)
    (inputs : PaperInformationThresholds f.natDegree R M (by omega) g0)
    (hloglo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (e : ∀ p : P, Q ≃ primeRootSet f p.val) (z : ℕ → Point) (a : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (i : ℕ) (hi : i ≤ paperCheckpointStop f.natDegree M (T : ℝ) (by have := inputs.two; omega))
    (hbefore : k ≤ paperMiddleStartPosition f M R m g0 T i P (batch.middle i)) :
    let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
    let hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
      (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
    ∀ v : ℕ, paperFullTailLaw z f.natDegree M g0 a k ν
      (paperFullTailCheckpointTime f.natDegree M g0 a k q hq ⁻¹' {v}) ≠ 0 →
      ((deficientCoordinates ((paperFullTailLaw z f.natDegree M g0 a k ν)[|
        paperFullTailCheckpointTime f.natDegree M g0 a k q hq ⁻¹' {v}])
        (fun p : P × Q => ZMod p.1.val)
        (fun p ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
          (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
        (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)).card : ℝ) ≤
          paperCoverageEta i * (P.card * (Fintype.card Q : ℝ)) := by
  let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
  have hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
    (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
  dsimp only
  intro v hv
  let νv := (pairedWalkPrefixLaw z (paperScheduleWindow f.natDegree M g0) a k q hbefore ν)[|
    pairedWalkTime (paperScheduleWindow f.natDegree M g0) a q ⁻¹' {v}]
  let : IsProbabilityMeasure νv := paperFullTailLaw_cond_next_time_probability z f.natDegree M g0
    a k q hbefore hq ν v hv
  have hcov := PaperJointBatch.coverage f hf hd R M m hm g0 c a0 l T hT bad P batch inputs
    hloglo hloghi e z a hstep hinj i hi q νv inferInstance le_rfl
  have hden : 0 < (P.card : ℝ) * (Fintype.card Q : ℝ) := by
    have hp : (0 : ℝ) < P.card := by exact_mod_cast batch.nonempty
    have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    positivity
  dsimp only [paperFullTailDeficientFraction] at hcov
  have hcount := (div_le_iff₀ hden).mp hcov
  rw [paperFullTailLaw_cond_next_time_deficientCoordinates z f.natDegree M g0 a k q hbefore hq ν v
    (fun p : P × Q => ZMod p.1.val) (fun p t => labelledPrimeResidue P (primeRootSet f) e p.1 p.2 (z t))]
  exact hcount

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.coverage
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.initial_coverage
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.conditional_coverage
