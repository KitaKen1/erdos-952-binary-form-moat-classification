import Integrations.SmoothedJointRoots435
import Integrations.PaperRootWordInputs435

set_option quotPrecheck false
noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- Apply the actual root-package joint bound to the SAME chosen geometric
family and ORIGINAL full-tail checkpoint. Word length, root selection,
separation, smoothing and physical forward shift are all DERIVED. Only
arithmetic avoidance and the arbitrary additive earlier-batch prior remain. -/
theorem PaperGridRootWordFamily.joint_word_information
    {A Q U : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    [∀ p : P j, NeZero p.val] (e : ∀ p : P j, Q ≃ primeRootSet f p.val)
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) (hz : Function.Injective z)
    (ψ : Point →+ U) (C : Finset (P j)) (label : P j → Q)
    (havoid : ∀ p ∈ P j, ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs)
    (hbefore : k ≤ paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j)
      ((fam.covered.family.batches j hj).2.middle 0)) :
    let batch := (fam.covered.family.batches j hj).2
    let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
    let hq : q < (paperScheduleList f.natDegree M g0).length :=
      paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
        (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let r := paperFullTailCheckpointTime f.natDegree M g0 a k q hq.le
    let u := paperFullTailTerminalTime f.natDegree M g0 a k
    let K := fun p : P j => ZMod p.val
    let φ := fun p : P j => labelledPrimeResidue (P j) (primeRootSet f) e p (label p)
    let E := fun p : P j => exactCheckpointBadEvent μ r (fun _ : Unit => ZMod p.val)
      (fun _ ω => φ p (z (u ω))) (paperCoverageTau 0) (paperCheckpointBeta f.natDegree 0) ()
    let V := fun (p : P j) ω => (φ p (z (r ω)), orderedPriorHom K φ ψ C p (z (r ω)))
    let β := paperCheckpointBeta f.natDegree 0
    let cost := fun p : P j => ((1 - β) * Real.log p.val + Real.log 6) +
      μ.real ((V p) ⁻¹' (posteriorBadData μ (V p) (E p) : Set _)) * (β * Real.log p.val)
    (condEntropy (fun ω => maskedPriorHom K φ C (z (r ω))) (fun ω => ψ (z (r ω))) μ -
      (∑ p ∈ C, cost p)) /
        paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β -
      4 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ) ≤
      condMutualInfo (fun v => maskedPriorHom K φ C (z v))
        (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
        (fun v => ψ (z v)) (μ.map u) := by
  let batch := (fam.covered.family.batches j hj).2
  let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
  have hq : q < (paperScheduleList f.natDegree M g0).length :=
    paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
      (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
  let N := terminalSmoothingLength (paperScheduleMaxT f.natDegree M)
  let W := paperScheduleWindow f.natDegree M g0
  let rest := (paperScheduleList f.natDegree M g0).length - k
  let Ω := PairedWalkSource A W (k + rest)
  let ν' := pairedWalkTailLaw z W a k ν rest
  let r : Ω → ℕ := fun ω => pairedWalkTime W a (k + (q - k))
    (pairedWalkCheckpoint W (k + rest) ⟨k + (q - k), by dsimp [rest]; omega⟩ ω)
  let b : Ω → ℕ := pairedWalkTime W a (k + rest)
  let S := paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)
  let ρ : ∀ p : P j, ZMod p.val := fun p => (e p (label p)).val
  have : NeZero N := ⟨(terminalSmoothingLength_pos _).ne'⟩
  have hr (ω : Ω × Fin N) : r ω.1 =
      paperFullTailCheckpointTime f.natDegree M g0 a k q hq.le ω := rfl
  have hu (ω : Ω × Fin N) : b ω.1 + ω.2.val =
      paperFullTailTerminalTime f.natDegree M g0 a k ω := rfl
  have hfwd (ω : Ω × Fin N) : r ω.1 ≤ b ω.1 + ω.2.val := by
    rw [hr, hu]
    exact (paperFullTailTerminalTime_checkpoint_bounds f.natDegree M g0 a k q hbefore hq ω).1
  have hsh (ω : Ω × Fin N) : b ω.1 + ω.2.val ≤ r ω.1 + S := by
    rw [hr, hu]
    exact (paperFullTailTerminalTime_checkpoint_bounds f.natDegree M g0 a k q hbefore hq ω).2
  have hT := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) fam.covered.spacing hj
  have hβ : 0 ≤ paperCheckpointBeta f.natDegree 0 := (paperCheckpointBeta_pos _ _ (by omega)).le
  have hβ₁ : paperCheckpointBeta f.natDegree 0 ≤ 1 := by
    simp only [paperCheckpointBeta, pow_zero]
    have hdR : (1 : ℝ) ≤ f.natDegree := by exact_mod_cast (by omega : 1 ≤ f.natDegree)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 200 * f.natDegree)]
    linarith
  have hi := smoothedRootPackage_joint_exact_gap_lower_bound ν' r b N z R S hstep hfwd hsh
    (P j) ρ ψ (rootWordLength f.natDegree (B ^ j)) f hf hd
    (fun p => (mem_primeRootSet f p.val (batch.primes p.val p.property).1 (ρ p)).mp (e p (label p)).property)
    hz (B ^ j) hT (rootWordLength_pos _ _)
    (fun p => (batch.primes p.val p.property).2.1)
    (fun p => (batch.primes p.val p.property).2.2.1)
    (fun p => (fam.word_inputs f hd R M B g0 c a0 l ε bad m P j hj p.val p.property
      (paperCoverageTau 0) (paperCoverageTau_bounds 0).1).2.2.1)
    (paperCoverageTau 0) (paperCheckpointBeta f.natDegree 0)
    (by linarith [(paperCoverageTau_bounds 0).1]) hβ hβ₁
    (fun p => (fam.word_inputs f hd R M B g0 c a0 l ε bad m P j hj p.val p.property
      (paperCoverageTau 0) (paperCoverageTau_bounds 0).1).2.2.2.1)
    (fun p => havoid p.val p.property) C
  exact hi

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.joint_word_information
