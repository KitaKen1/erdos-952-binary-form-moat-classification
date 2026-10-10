import Integrations.PosteriorBadData435
import Integrations.PaperPosteriorFavorable435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- ACTUAL backward coverage controls EACH coordinate's OWN bad-data law.
The data can vary with the target, subset and full root assignment. In particular
chain-rule prefix data need not equal the full selected-tuple data. -/
theorem PaperJointBatch.coordinate_bad_data
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
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
    (hbefore : k ≤ paperMiddleStartPosition f M R m g0 T i P (batch.middle i))
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ P.card)
    (D : P → Type*) [∀ p, Fintype (D p)] [∀ p, MeasurableSpace (D p)]
    [∀ p, MeasurableSingletonClass (D p)]
    (V : Finset P → (P → Q) → ∀ p, PaperFullTailSource A f.natDegree M g0 k → D p) :
    let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
    let hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
      (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let t := paperFullTailCheckpointTime f.natDegree M g0 a k q hq
    let E := exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val)
      (fun p ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
        (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
      (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)
    subsetLabelAverage s (fun S ρ => ∑ p ∈ S,
      μ.real ((V S ρ p) ⁻¹' (posteriorBadData μ (V S ρ p) (E (p, ρ p)) : Set (D p)))) ≤
        2 * paperCoverageEta i * s := by
  let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
  have hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
    (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
  let μ := paperFullTailLaw z f.natDegree M g0 a k ν
  let t := paperFullTailCheckpointTime f.natDegree M g0 a k q hq
  let X := fun (p : P × Q) ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
    (z (paperFullTailTerminalTime f.natDegree M g0 a k ω))
  let B := fun v : Fin (finiteTimeBound t) => deficientCoordinates (μ[|t ⁻¹' {v.val}])
    (fun p : P × Q => ZMod p.1.val) X (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)
  have hmean := badCoordinateEvents_sum_le μ (finiteTimeCheckpoint t) (measurable_of_finite _)
    B (paperCoverageEta i) (by
      intro v hv
      rw [finiteTimeCheckpoint_fiber] at hv
      simpa only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul] using
        PaperJointBatch.conditional_coverage f hf hd R M m hm g0 c a0 l T hT bad P batch inputs
          hloglo hloghi e z a k ν hstep hinj i hi hbefore v.val hv)
  have hden : 0 < (P.card : ℝ) * (Fintype.card Q : ℝ) := by
    have hp : (0 : ℝ) < P.card := by exact_mod_cast batch.nonempty
    have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    positivity
  dsimp only
  apply subsetLabelAverage_coordinateBadData_le D μ s hs (by simpa using hsk) V
    (fun p r => exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val) X
      (paperCoverageTau i) (paperCheckpointBeta f.natDegree i) (p, r)) (paperCoverageEta i)
  apply (div_le_iff₀ (by simpa using hden)).mpr
  simpa only [B, exactCheckpointBadEvent, finiteTimeCheckpoint_val,
    Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Fintype.sum_prod_type] using hmean

/-- The bad-data logarithmic information loss for ACTUAL dyadic prime
coordinates is at most 2*eta_i*s*log(2*T), including target-dependent prior maps.
The loss is averaged under each map's original data law, not a shared posterior. -/
theorem PaperJointBatch.coordinate_bad_log_cost
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
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
    (hbefore : k ≤ paperMiddleStartPosition f M R m g0 T i P (batch.middle i))
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ P.card)
    (D : P → Type*) [∀ p, Fintype (D p)] [∀ p, MeasurableSpace (D p)]
    [∀ p, MeasurableSingletonClass (D p)]
    (V : Finset P → (P → Q) → ∀ p, PaperFullTailSource A f.natDegree M g0 k → D p) :
    let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
    let hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
      (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let t := paperFullTailCheckpointTime f.natDegree M g0 a k q hq
    let E := exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val)
      (fun p ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
        (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
      (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)
    subsetLabelAverage s (fun S ρ => ∑ p ∈ S,
      μ.real ((V S ρ p) ⁻¹' (posteriorBadData μ (V S ρ p) (E (p, ρ p)) : Set (D p))) * Real.log p.val) ≤
        2 * paperCoverageEta i * s * Real.log (2 * T : ℕ) := by
  let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
  have hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
    (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
  let μ := paperFullTailLaw z f.natDegree M g0 a k ν
  let t := paperFullTailCheckpointTime f.natDegree M g0 a k q hq
  let E := exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val)
    (fun p ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
      (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
    (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)
  let w := fun (S : Finset P) (ρ : P → Q) (p : P) =>
    μ.real ((V S ρ p) ⁻¹' (posteriorBadData μ (V S ρ p) (E (p, ρ p)) : Set (D p)))
  have hraw := PaperJointBatch.coordinate_bad_data f hf hd R M m hm g0 c a0 l T hT bad P
    batch inputs hloglo hloghi e z a k ν hstep hinj i hi hbefore s hs hsk D V
  change subsetLabelAverage s (fun S ρ => ∑ p ∈ S, w S ρ p) ≤ 2 * paperCoverageEta i * s at hraw
  change subsetLabelAverage s (fun S ρ => ∑ p ∈ S, w S ρ p * Real.log p.val) ≤ _
  have hlog : 0 ≤ Real.log (2 * T : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * T))
  apply (subsetLabelAverage_mono s _
    (fun S ρ => ∑ p ∈ S, w S ρ p * Real.log (2 * T : ℕ)) ?_).trans
  · convert mul_le_mul_of_nonneg_right hraw hlog using 1
    unfold subsetLabelAverage
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.sum_div]
    simp_rw [← Finset.sum_mul]
    ring
  · intro S _ ρ
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (show 0 ≤ w S ρ p from measureReal_nonneg)
    apply Real.log_le_log
    · exact_mod_cast (by have := (batch.primes p.val p.property).2.1; omega : 0 < p.val)
    · exact_mod_cast (batch.primes p.val p.property).2.2.1

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.coordinate_bad_data

#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.coordinate_bad_log_cost
