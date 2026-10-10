import Integrations.PosteriorFavorable435
import Integrations.PaperJointCoverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A bad-coordinate set depending on an exact finite fiber averages with
that fiber's ORIGINAL mass. Only positive fibers need cardinal bounds. -/
theorem badCoordinateEvents_sum_le {Ω D C : Type*} [MeasurableSpace Ω]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [Fintype C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → D) (hV : Measurable V)
    (B : D → Finset C) (η : ℝ)
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ((B a).card : ℝ) ≤ η * Fintype.card C) :
    (∑ c, μ.real {ω | c ∈ B (V ω)}) ≤ η * Fintype.card C := by
  have he (c : C) : μ.real {ω | c ∈ B (V ω)} =
      ∑ a, if c ∈ B a then μ.real (V ⁻¹' {a}) else 0 := by
    let S := Finset.univ.filter (fun a => c ∈ B a)
    have hs : {ω | c ∈ B (V ω)} = V ⁻¹' (S : Set D) := by ext ω; simp [S]
    rw [hs, ← sum_measureReal_preimage_singleton S (fun a _ => hV (MeasurableSet.singleton a))]
    exact Finset.sum_filter _ _
  simp_rw [he]
  rw [Finset.sum_comm]
  have hc (a : D) : (∑ c, if c ∈ B a then μ.real (V ⁻¹' {a}) else 0) =
      μ.real (V ⁻¹' {a}) * ((B a).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [hc]
  calc
    _ ≤ ∑ a, μ.real (V ⁻¹' {a}) * (η * Fintype.card C) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : μ (V ⁻¹' {a}) = 0
      · simp [measureReal_def, ha]
      · exact mul_le_mul_of_nonneg_left (hbad a ha) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, fiber_weights_sum_one μ V hV, one_mul]

/-- Bad coverage at the ORIGINAL exact checkpoint time of a sample.
The event is fixed for each prime/root coordinate before auxiliary choices. -/
def exactCheckpointBadEvent {Ω C : Type*} [MeasurableSpace Ω] [Fintype C]
    (μ : Measure Ω) (t : Ω → ℕ) (G : C → Type*) [∀ c, Fintype (G c)]
    (X : ∀ c, Ω → G c) (τ β : ℝ) (c : C) : Set Ω :=
  {ω | c ∈ deficientCoordinates (μ[|t ⁻¹' {t ω}]) G X τ β}

/-- ACTUAL same-batch coverage supplies the prior bad-event budget, so the
paper's 2*eta_i*s posterior unfavorable bound is a CONCLUSION. Residue data
may depend on the whole auxiliary subset/label choice; no independence is
assumed after conditioning. All laws are the SAME full terminal experiment. -/
theorem PaperJointBatch.posterior_unfavorable
    {A Q D : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
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
    (V : Finset P → (P → Q) → PaperFullTailSource A f.natDegree M g0 k → D) :
    let q := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
    let hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
      (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let t := paperFullTailCheckpointTime f.natDegree M g0 a k q hq
    let E := exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val)
      (fun p ω => labelledPrimeResidue P (primeRootSet f) e p.1 p.2
        (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
      (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)
    subsetLabelAverage s (fun S ρ => ∑ v, μ.real ((V S ρ) ⁻¹' {v}) *
      ((posteriorUnfavorable μ (V S ρ) v S (fun p => E (p, ρ p))).card : ℝ)) ≤
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
  apply subsetLabelAverage_posteriorUnfavorable_le μ s hs (by simpa using hsk) V
    (fun p r => exactCheckpointBadEvent μ t (fun p : P × Q => ZMod p.1.val) X
      (paperCoverageTau i) (paperCheckpointBeta f.natDegree i) (p, r)) (paperCoverageEta i)
  apply (div_le_iff₀ (by simpa using hden)).mpr
  simpa only [B, exactCheckpointBadEvent, finiteTimeCheckpoint_val,
    Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Fintype.sum_prod_type] using hmean

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.badCoordinateEvents_sum_le
#print axioms BinaryFormMoat.GeometryIntegration.exactCheckpointBadEvent
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.posterior_unfavorable
