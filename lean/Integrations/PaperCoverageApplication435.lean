import Integrations.PaperCoverageBudgets435
import Integrations.WalkCoverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Apply the paper's numerical choices to the ACTUAL finite walk law.
Only the structural checkpoint entropy, native alphabet/record mass and
conditional next-coverage inputs remain; every scalar transfer budget is
derived. Trials are the constructed Fin n_i experiment, not extra independent
coordinates assumed on the original walk law. -/
theorem paper_walk_one_step_coverage_transfer
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
    {timeBound : ℕ} (t : Ω → Fin timeBound) (u : Ω → ℕ)
    (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ P.card)
    (hjoint : (1 - Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3)) * (s : ℝ) *
      coordinateLogMean (fun c : P × Q => ZMod c.1.val) ≤
        labelSubsetJointEntropy μ (fun c : P × Q => ZMod c.1.val)
          (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (t ω).val)) s)
    (halphabet : 2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) * paperCheckpointTarget d T (i + 1))
    (hmass : Real.exp (paperCheckpointRadius d i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤
      (s : ℝ) * primeBatchLogMean P)
    (hnext : ∀ a, μ (t ⁻¹' {a}) ≠ 0 →
      ((deficientCoordinates (μ[|t ⁻¹' {a}]) (fun c : P × Q => ZMod c.1.val)
        (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (u ω)))
          (paperCoverageTau (i + 1)) (paperCheckpointBeta d (i + 1))).card : ℝ) ≤
            paperCoverageEta (i + 1) * Fintype.card (P × Q)) :
    ((deficientCoordinates μ (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (u ω)))
        (paperCoverageTau i) (paperCheckpointBeta d i)).card : ℝ) /
          (P.card * (Fintype.card Q : ℝ)) ≤ paperCoverageEta i := by
  have hmar := (paperCoverageMarginsThreshold_spec d hd).2 M hmargin hM (T : ℝ)
    (by exact_mod_cast hT) hlog i hi
  have hC : 0 < 4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega))
    linarith
  have hmean : coordinateLogMean (fun c : P × Q => ZMod c.1.val) = primeBatchLogMean P := by
    rw [rootResidue_coordinateLogMean]
    simp only [primeBatchLogMean, Fintype.card_coe]
  have hdBudget := paperCoverageSharedData_budget d hd M hM (T : ℝ)
    (by exact_mod_cast (show 1 ≤ T by omega)) i hi _ hC hshared _ ((s : ℝ) * primeBatchLogMean P)
    halphabet hmass
  have hd' : (Fintype.card (Fin (paperCoverageTrials d T i)) : ℝ) *
      (2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ)) ≤
        Real.exp (-(M : ℝ) ^ 3) * (s : ℝ) * coordinateLogMean (fun c : P × Q => ZMod c.1.val) := by
    simpa only [Fintype.card_fin, hmean, mul_assoc] using hdBudget
  have hβmax : paperCheckpointBeta d (i + 1) ≤ 2 := by
    have h := paperCheckpointBeta_antitone d hd (Nat.zero_le (i + 1))
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hz : paperCheckpointBeta d 0 ≤ 2 := by
      norm_num only [paperCheckpointBeta, pow_zero]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact h.trans hz
  have hscale : coordinateLogMean (fun c : P × Q => ZMod c.1.val) ≤ 2 * Real.log T := by
    rw [hmean]
    have h := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.2.1
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ T by exact_mod_cast hT)
    push_cast at h
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (show T ≠ 0 by omega))] at h
    linarith
  have hn := paperCoverageTrials_pos d hd (T : ℝ) (by exact_mod_cast (show 1 ≤ T by omega)) i
  have htailAll (c : P × Q) : (Fintype.card (ZMod c.1.val) : ℝ) *
      Real.exp (-(paperCoverageDelta i) ^ 2 * (Fintype.card (Fin (paperCoverageTrials d T i)) : ℝ) *
        (Fintype.card (ZMod c.1.val) : ℝ) ^ (-paperCheckpointBeta d i) / 2) ≤ paperCoverageDelta i / 100 := by
    simpa only [ZMod.card, Fintype.card_fin] using
      (paperCoverageTailThreshold_spec d hd).2 M htail hM (T : ℝ) (by exact_mod_cast hT) hlog i hi
        (c.1.val : ℝ) (by exact_mod_cast hlo c.1.val c.1.property) (by exact_mod_cast hhi c.1.val c.1.property)
  have hprimeAll (c : P × Q) : Real.log T ≤ Real.log (Fintype.card (ZMod c.1.val)) := by
    simp only [ZMod.card]
    exact Real.log_le_log (by exact_mod_cast (show 0 < T by omega)) (by exact_mod_cast hlo c.1.val c.1.property)
  have h := walk_one_step_coverage_transfer μ z R S hstep t u hforward hshift
    (fun c : P × Q => ZMod c.1.val) (fun c => labelledPrimeResidue P roots e c.1 c.2)
    (J := Fin (paperCoverageTrials d T i)) ⟨0, hn⟩ s hs (by simpa only [Fintype.card_coe] using hsk)
    (Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3)) (Real.exp (-(M : ℝ) ^ 3)) hjoint hd'
    (paperCoverageTau i) (paperCoverageDelta i) (paperCheckpointBeta d i)
    (paperCheckpointBeta d (i + 1)) (Real.log T) (paperCoverageEta i) (paperCoverageEta (i + 1))
    (by linarith [(paperCoverageTau_bounds i).1]) (paperCoverageTau_bounds i).2.le
    (paperCoverageDelta_pos i) (paperCoverageDelta_le i) (paperCheckpointBeta_pos d i hd).le
    (paperCheckpointBeta_pos d (i + 1) hd) hβmax (Real.log_pos (by exact_mod_cast (show 1 < T by omega)))
    (paperCoverageEta_pos i).le (by simpa only [paperCoverageTau_succ] using hnext)
    (by rw [paperCoverageEta_succ])
    (fun c => by simpa only [ZMod.card] using hmar.2.1 c.1.val (by exact_mod_cast hlo c.1.val c.1.property))
    htailAll hprimeAll hmar.2.2 hscale (by positivity) hmar.1
  simpa only [Fintype.card_coe] using h

/-- The SAME selected good-prime batch supplies all middle/bottom
certificates, terminal coverage, every scalar transfer threshold and ALL
native future bounds, before any walk, source, law or exact start. -/
theorem paperSchedule_middle_bottom_transfer_ready_batches (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∃ M0 : ℕ, 2 ≤ M0 ∧ paperMiddleAccuracyThreshold ≤ M0 ∧
      paperTerminalCoverageThreshold f.natDegree (by omega) ≤ M0 ∧
      paperCoverageMarginsThreshold f.natDegree (by omega) ≤ M0 ∧
      paperCoverageTailThreshold f.natDegree (by omega) ≤ M0 ∧
      paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
        (by have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega)); linarith) ≤ M0 ∧
      (∀ M ≥ M0, ∀ o ∈ paperScheduledOps f.natDegree M g0,
        Real.log (paperFutureShift o + 1 : ℕ) ≤ 2 * (paperOpG o * paperOpU o)) ∧
      ∀ M ≥ M0, ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℕ, 2 ≤ T →
        paperScheduleX f.natDegree m.val ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
        ∃ P : Finset ℕ, P.card = paperPrimeCount c T ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
          0 < P.card ∧ (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
          (∀ i : ℕ, PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
            (paperMiddleIterations M) P) ∧
          PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
            (paperBottomIterations M) P := by
  obtain ⟨c, hc, hs⟩ := paperSchedule_middle_bottom_coverage_ready_batches f hf hd R g0 hg0 hg064
  obtain ⟨Mf, hfut⟩ := paperSchedule_uniform_future_shift f.natDegree (by omega) g0 hg0 (by linarith)
  have hC : 0 < 4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
    have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega))
    linarith
  refine ⟨c, hc, ?_⟩
  intro bad
  obtain ⟨Mb, hMb2, hacc, hbase, hb⟩ := hs bad
  let Ma := paperCoverageMarginsThreshold f.natDegree (by omega)
  let Mt := paperCoverageTailThreshold f.natDegree (by omega)
  let Ms := paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) hC
  refine ⟨Mb + Ma + Mt + Ms + Mf, by omega, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro M hM
    exact hfut M (by omega)
  · intro M hM
    exact hb M (by omega)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paper_walk_one_step_coverage_transfer
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_middle_bottom_transfer_ready_batches
