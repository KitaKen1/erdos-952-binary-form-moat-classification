import Integrations.PaperMiddleWitness435
import Integrations.PaperFullTailCheckpoint435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Constructed middle certificates supply ALL structural entropy/rank/mass
inputs on the SAME full terminal source. No joint-entropy lower bound, rank
positivity, capacity or recorded mass is a hypothesis. -/
theorem paperMiddleCertificate_full_terminal_inputs
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T i : ℕ)
    (hM : 2 ≤ M) (hacc : paperMiddleAccuracyThreshold ≤ M)
    (hi : i < paperCheckpointStop f.natDegree M (T : ℝ) (by omega))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (roots : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (roots p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ roots p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ roots p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hloglo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (next : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T (i + 1))
      (paperMiddleIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0)) [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperMiddleStartPosition f M R m g0 T i P cert)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let r := paperMiddleStartPosition f M R m g0 T (i + 1) P next
    let hr := (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T (i + 1) P next)).le
    let q := paperMiddleRecordRank f M m g0 T i P
    1 ≤ q ∧ q ≤ P.card ∧
      Real.exp (paperCheckpointRadius f.natDegree i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤
        (q : ℝ) * primeBatchLogMean P ∧
      (1 - Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3)) * (q : ℝ) *
        coordinateLogMean (fun c : P × Q => ZMod c.1.val) ≤
          labelSubsetJointEntropy (paperFullTailLaw z f.natDegree M g0 a k0 ν)
            (fun c : P × Q => ZMod c.1.val)
            (fun c ω => labelledPrimeResidue P roots e c.1 c.2
              (z (paperFullTailCheckpointTime f.natDegree M g0 a k0 r hr ω))) q := by
  dsimp only
  have hloc := paperMiddleTarget_log_hi f.natDegree m.val (by omega) (T : ℝ) hloglo hloghi i
  have hq := paperMiddleRecordRank_bounds f M R m g0 T i P (by omega) hT hPk hlo hhi cert
  have hmass := paperMiddleCertificate_record_mass f M R m g0 T i P (by omega) hT hPk hlo hhi hloc cert
  refine ⟨hq.1, hq.2, hmass, ?_⟩
  dsimp only [paperMiddleStartPosition]
  rw [paperFullTailLaw_checkpoint_jointEntropy z f.natDegree M g0 a k0 _ _ ν
    (fun c : P × Q => ZMod c.1.val)
    (fun c x => labelledPrimeResidue P roots e c.1 c.2 x)]
  have high := paperMiddleCertificate_next_entropy f hf hd M R m hm g0 T i hM hacc hi
    P hP roots hcard hroot e hT hPk hlo hhi hloc cert next z a k0 ν hbefore hstep hinj
  have hL : 0 < primeBatchLogMean P := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hmassP : 0 < (paperMiddleRecordRank f M m g0 T i P : ℝ) * primeBatchLogMean P := by
    have hqP : (0 : ℝ) < paperMiddleRecordRank f M m g0 T i P := by exact_mod_cast (show 0 < paperMiddleRecordRank f M m g0 T i P by omega)
    exact mul_pos hqP hL
  have hh := (le_div_iff₀ hmassP).mp high
  have hmean : coordinateLogMean (fun c : P × Q => ZMod c.1.val) = primeBatchLogMean P := by
    rw [rootResidue_coordinateLogMean]
    simp only [primeBatchLogMean, Fintype.card_coe]
  rw [hmean]
  simp only [paperMiddleRecordRank, paperMiddleStartOp,
    labelledPointEntropyMean_eq_joint, mul_assoc] at hh ⊢
  exact hh

/-- The actual common terminal law satisfies one-step coverage with ALL
structural inputs supplied by the paper's middle certificates and future
supplier. ONLY coverage on its original positive NEXT-time fibers remains. -/
theorem paperMiddleCertificate_full_terminal_coverage_step
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T i : ℕ)
    (hM : 2 ≤ M) (hacc : paperMiddleAccuracyThreshold ≤ M)
    (hi : i < paperCheckpointStop f.natDegree M (T : ℝ) (by omega))
    (hmargin : paperCoverageMarginsThreshold f.natDegree (by omega) ≤ M)
    (htail : paperCoverageTailThreshold f.natDegree (by omega) ≤ M)
    (hshared : paperCoverageSharedDataThreshold (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
      (by have h : 0 ≤ Real.log (2 * (R + 1) + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (R + 1) + 1 by omega)); linarith) ≤ M)
    (hfuture : ∀ o ∈ paperScheduledOps f.natDegree M g0,
      Real.log (paperFutureShift o + 1 : ℕ) ≤ 2 * (paperOpG o * paperOpU o))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (roots : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (roots p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ roots p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ roots p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hloglo : paperScheduleX f.natDegree m.val ≤ Real.log T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (next : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T (i + 1))
      (paperMiddleIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0)) [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperMiddleStartPosition f M R m g0 T i P cert)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (hnext :
      let r := paperMiddleStartPosition f M R m g0 T (i + 1) P next
      let hr := (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T (i + 1) P next)).le
      let μ := paperFullTailLaw z f.natDegree M g0 a k0 ν
      let t := paperFullTailCheckpointTime f.natDegree M g0 a k0 r hr
      ∀ b : ℕ, μ (t ⁻¹' {b}) ≠ 0 →
        ((deficientCoordinates (μ[|t ⁻¹' {b}]) (fun c : P × Q => ZMod c.1.val)
          (fun c ω => labelledPrimeResidue P roots e c.1 c.2
            (z (paperFullTailTerminalTime f.natDegree M g0 a k0 ω)))
              (paperCoverageTau (i + 1)) (paperCheckpointBeta f.natDegree (i + 1))).card : ℝ) ≤
                paperCoverageEta (i + 1) * Fintype.card (P × Q)) :
    ((deficientCoordinates (paperFullTailLaw z f.natDegree M g0 a k0 ν)
      (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P roots e c.1 c.2
        (z (paperFullTailTerminalTime f.natDegree M g0 a k0 ω)))
          (paperCoverageTau i) (paperCheckpointBeta f.natDegree i)).card : ℝ) /
            (P.card * (Fintype.card Q : ℝ)) ≤ paperCoverageEta i := by
  let : MeasurableSpace Q := ⊤
  let : MeasurableSingletonClass Q := inferInstance
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSingletonClass Bool := inferInstance
  let o := paperMiddleStartOp f M R m g0 T (i + 1) P next
  let r := paperMiddleStartPosition f M R m g0 T (i + 1) P next
  have ho := paperMiddleStartOp_mem f M R m hm g0 T (i + 1) P next
  have hr : r < (paperScheduleList f.natDegree M g0).length := paperOpPosition_lt o ho
  let t := paperFullTailCheckpointTime f.natDegree M g0 a k0 r hr.le
  let u := paperFullTailTerminalTime f.natDegree M g0 a k0
  have hloc := paperMiddleTarget_log_hi f.natDegree m.val (by omega) (T : ℝ) hloglo hloghi i
  have horder := paperMiddleCertificate_before_next f (by omega) M R m hm g0 T i P hM hi hloc cert next
  have hkr : k0 ≤ r := by
    have hpos := paperBlockOp_position g0 m hm 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) cert.fit
    dsimp [r, paperMiddleStartPosition, paperMiddleStartOp] at *
    omega
  have hget : (paperScheduleList f.natDegree M g0).get ⟨r, hr⟩ = o := paperOpPosition_get o ho
  have htimes (ω : PaperFullTailSource A f.natDegree M g0 k0) : t ω ≤ u ω ∧ u ω ≤ t ω + paperFutureShift o := by
    have h := paperFullTailTerminalTime_checkpoint_bounds f.natDegree M g0 a k0 r hkr hr ω
    rwa [hget] at h
  have hinputs := paperMiddleCertificate_full_terminal_inputs f hf hd M R m hm g0 T i hM hacc hi
    P hP roots hcard hroot e hT hPk hlo hhi hloglo hloghi cert next z a k0 ν hbefore hstep hinj
  have halpha := paperMiddleStart_native_alphabet f (by omega) M R m hm g0 T (i + 1) P hT
    hloglo hloghi next hfuture
  have hlogM : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree M :=
    hloghi.trans (mul_le_mul_of_nonneg_left (paperScheduleX_mono f.natDegree (by omega) (show m.val ≤ M by omega)) (by norm_num))
  exact paper_walk_nat_checkpoint_coverage_transfer f.natDegree M R (paperFutureShift o) T i (by omega)
    (by omega) hT hlogM hi hmargin htail hshared P hPk hlo hhi roots e
    (paperFullTailLaw z f.natDegree M g0 a k0 ν) z hstep t u
    (fun ω => (htimes ω).1) (fun ω => (htimes ω).2)
    (paperMiddleRecordRank f M m g0 T i P) hinputs.1 hinputs.2.1 hinputs.2.2.2 halpha hinputs.2.2.1 hnext

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCertificate_full_terminal_inputs
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCertificate_full_terminal_coverage_step
