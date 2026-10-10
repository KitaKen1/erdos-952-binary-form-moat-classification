import Integrations.PaperCoverageApplication435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A finite source bounds its actual natural checkpoint times, without an
extra physical-time bound in the theorem statement. -/
def finiteTimeBound {Ω : Type*} [Fintype Ω] (t : Ω → ℕ) : ℕ := (∑ ω, t ω) + 1

def finiteTimeCheckpoint {Ω : Type*} [Fintype Ω] (t : Ω → ℕ) (ω : Ω) : Fin (finiteTimeBound t) :=
  ⟨t ω, by
    have h : t ω ≤ ∑ a, t a := Finset.single_le_sum (fun a _ => Nat.zero_le (t a)) (Finset.mem_univ ω)
    unfold finiteTimeBound
    omega⟩

theorem finiteTimeCheckpoint_val {Ω : Type*} [Fintype Ω] (t : Ω → ℕ) (ω : Ω) :
    (finiteTimeCheckpoint t ω).val = t ω := rfl

/-- Exact fibers, including times outside the actual range. No new law or
conditioning event is introduced by the finite encoding. -/
theorem finiteTimeCheckpoint_fiber {Ω : Type*} [Fintype Ω] (t : Ω → ℕ)
    (a : Fin (finiteTimeBound t)) :
    (finiteTimeCheckpoint t) ⁻¹' {a} = t ⁻¹' {a.val} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, finiteTimeCheckpoint_val]

/-- The paper's actual one-step transfer accepts natural checkpoint times
on any finite source. Finite encoding preserves every original conditional
fiber and the actual checkpoint residue variable. -/
theorem paper_walk_nat_checkpoint_coverage_transfer
    {Ω Q : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (d M R S T i : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (hT : 2 ≤ T)
    (hlog : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M)
    (hi : i < paperCheckpointStop d M (T : ℝ) hM)
    (hmargin : paperCoverageMarginsThreshold d hd ≤ M)
    (htail : paperCoverageTailThreshold d hd ≤ M)
    (hshared : paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
      (by have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega)); linarith) ≤ M)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (roots : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ roots p.val)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (t u : Ω → ℕ) (hforward : ∀ ω, t ω ≤ u ω) (hshift : ∀ ω, u ω ≤ t ω + S)
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ P.card)
    (hjoint : (1 - Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3)) * (s : ℝ) *
      coordinateLogMean (fun c : P × Q => ZMod c.1.val) ≤
        labelSubsetJointEntropy μ (fun c : P × Q => ZMod c.1.val)
          (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (t ω))) s)
    (halphabet : 2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) * paperCheckpointTarget d T (i + 1))
    (hmass : Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤
      (s : ℝ) * primeBatchLogMean P)
    (hnext : ∀ a : ℕ, μ (t ⁻¹' {a}) ≠ 0 →
      ((deficientCoordinates (μ[|t ⁻¹' {a}]) (fun c : P × Q => ZMod c.1.val)
        (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (u ω)))
          (paperCoverageTau (i + 1)) (paperCheckpointBeta d (i + 1))).card : ℝ) ≤
            paperCoverageEta (i + 1) * Fintype.card (P × Q)) :
    ((deficientCoordinates μ (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (u ω)))
        (paperCoverageTau i) (paperCheckpointBeta d i)).card : ℝ) /
          (P.card * (Fintype.card Q : ℝ)) ≤ paperCoverageEta i := by
  apply paper_walk_one_step_coverage_transfer d M R S T i hd hM hT hlog hi hmargin htail hshared
    P hPk hlo hhi roots e μ z hstep (finiteTimeCheckpoint t) u hforward hshift s hs hsk
    hjoint halphabet hmass
  intro a ha
  rw [finiteTimeCheckpoint_fiber] at ha ⊢
  exact hnext a.val ha

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.finiteTimeBound
#print axioms BinaryFormMoat.GeometryIntegration.finiteTimeCheckpoint
#print axioms BinaryFormMoat.GeometryIntegration.finiteTimeCheckpoint_val
#print axioms BinaryFormMoat.GeometryIntegration.finiteTimeCheckpoint_fiber
#print axioms BinaryFormMoat.GeometryIntegration.paper_walk_nat_checkpoint_coverage_transfer
