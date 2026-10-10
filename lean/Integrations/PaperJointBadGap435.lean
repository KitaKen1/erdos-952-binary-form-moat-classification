import Integrations.PaperCoordinateBadData435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The beta-scaled bad-data logarithmic information loss for ACTUAL dyadic prime
coordinates is at most 2*eta_i*s*beta_i*log(2*T), including target-dependent prior maps.
The loss is averaged under each map's original data law, not a shared posterior. -/
theorem PaperJointBatch.coordinate_bad_beta_log_cost
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
      μ.real ((V S ρ p) ⁻¹' (posteriorBadData μ (V S ρ p) (E (p, ρ p)) : Set (D p))) *
        (paperCheckpointBeta f.natDegree i * Real.log p.val)) ≤
        2 * paperCoverageEta i * s * Real.log (2 * T : ℕ) * paperCheckpointBeta f.natDegree i := by
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
  have hraw := PaperJointBatch.coordinate_bad_log_cost f hf hd R M m hm g0 c a0 l T hT bad P
    batch inputs hloglo hloghi e z a k ν hstep hinj i hi hbefore s hs hsk D V
  change subsetLabelAverage s (fun S ρ => ∑ p ∈ S, w S ρ p * Real.log p.val) ≤
    2 * paperCoverageEta i * s * Real.log (2 * T : ℕ) at hraw
  change subsetLabelAverage s (fun S ρ => ∑ p ∈ S, w S ρ p *
    (paperCheckpointBeta f.natDegree i * Real.log p.val)) ≤ _
  calc
    _ = subsetLabelAverage s (fun S ρ => ∑ p ∈ S, w S ρ p * Real.log p.val) *
        paperCheckpointBeta f.natDegree i := by
      have he (S : Finset P) (ρ : P → Q) (p : P) :
          w S ρ p * (paperCheckpointBeta f.natDegree i * Real.log p.val) =
          (w S ρ p * Real.log p.val) * paperCheckpointBeta f.natDegree i := by ring
      unfold subsetLabelAverage
      simp only [he, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro ρ _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hraw (paperCheckpointBeta_pos f.natDegree i (by omega)).le

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.coordinate_bad_beta_log_cost
