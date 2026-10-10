import Integrations.PaperConditionalCoverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Actual terminal deficient fraction at the paper's exact i-th thresholds. -/
def paperFullTailDeficientFraction {A Q : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype Q]
    (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (roots : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ roots p.val)
    (z : ℕ → Point) (d M : ℕ) (g0 : ℝ) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) (i : ℕ) : ℝ :=
  ((deficientCoordinates (paperFullTailLaw z d M g0 a k ν) (fun c : P × Q => ZMod c.1.val)
    (fun c ω => labelledPrimeResidue P roots e c.1 c.2 (z (paperFullTailTerminalTime d M g0 a k ω)))
      (paperCoverageTau i) (paperCheckpointBeta d i)).card : ℝ) / (P.card * (Fintype.card Q : ℝ))

/-- The bottom certificate supplies the actual base case for EVERY probability
law at or before the final middle checkpoint, with no coverage hypothesis. -/
theorem paperMiddleBottomCertificates_full_terminal_base
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T : ℕ)
    (hM : 1 ≤ M) (hbase : paperTerminalCoverageThreshold f.natDegree (by omega) ≤ M)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (roots : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (roots p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ roots p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ roots p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hloghi : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (cert : PaperBlockCertificate f R M m g0 1
      (paperCheckpointTarget f.natDegree T (paperCheckpointStop f.natDegree M (T : ℝ) hM))
      (paperMiddleIterations M) P)
    (bottom : PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
      (paperBottomIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k)) [IsProbabilityMeasure ν]
    (hbefore : k ≤ paperMiddleStartPosition f M R m g0 T
      (paperCheckpointStop f.natDegree M (T : ℝ) hM) P cert)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    paperFullTailDeficientFraction P roots e z f.natDegree M g0 a k ν
      (paperCheckpointStop f.natDegree M (T : ℝ) hM) ≤
        paperCoverageEta (paperCheckpointStop f.natDegree M (T : ℝ) hM) := by
  have hmb : paperMiddleStartPosition f M R m g0 T
      (paperCheckpointStop f.natDegree M (T : ℝ) hM) P cert ≤
      paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 2
        (paperBottomTarget f.natDegree m.val) 0 (by have := bottom.fit; omega)) := by
    dsimp only [paperMiddleStartPosition]
    rw [paperMiddleStartOp_eq_checkpoint]
    exact paperMiddleCheckpoint_before_bottom g0 m hm T _ _ (by have := bottom.fit; omega)
  exact (paperBottomCertificate_terminal_coverage f hf hd M R m hm g0 T hM P hP roots hcard hroot e hT hPk hlo hhi bottom z a k ν
    (hbefore.trans hmb) hstep hinj hloghi hbase).le

/-- Backward coverage is proved for ANY law at ANY earlier checkpoint. This
strengthening supplies the original positive NEXT-time fibers by actual restart,
so no conditional coverage or abstract recurrence is an input. -/
theorem paperMiddleBottomCertificates_backward_coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T : ℕ)
    (hM : 2 ≤ M) (hacc : paperMiddleAccuracyThreshold ≤ M)
    (hbase : paperTerminalCoverageThreshold f.natDegree (by omega) ≤ M)
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
    (cert : ∀ i : ℕ, PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (bottom : PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
      (paperBottomIterations M) P)
    (z : ℕ → Point) (a : A → ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    ∀ i ≤ paperCheckpointStop f.natDegree M (T : ℝ) (by omega), ∀ k : ℕ,
      ∀ ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k),
        IsProbabilityMeasure ν → k ≤ paperMiddleStartPosition f M R m g0 T i P (cert i) →
          paperFullTailDeficientFraction P roots e z f.natDegree M g0 a k ν i ≤ paperCoverageEta i := by
  let J := paperCheckpointStop f.natDegree M (T : ℝ) (by omega)
  have hden : 0 < (P.card : ℝ) * (Fintype.card Q : ℝ) := by
    have hp : (0 : ℝ) < P.card := by exact_mod_cast hPk
    have hq : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    exact mul_pos hp hq
  have descend : ∀ n i : ℕ, i + n = J → ∀ k : ℕ,
      ∀ ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k),
        IsProbabilityMeasure ν → k ≤ paperMiddleStartPosition f M R m g0 T i P (cert i) →
          paperFullTailDeficientFraction P roots e z f.natDegree M g0 a k ν i ≤ paperCoverageEta i := by
    intro n
    induction n with
    | zero =>
      intro i he k ν hν hbefore
      have hi : i = J := by omega
      subst i
      let : IsProbabilityMeasure ν := hν
      exact paperMiddleBottomCertificates_full_terminal_base f hf hd M R m hm g0 T (by omega)
        hbase P hP roots hcard hroot e hT hPk hlo hhi hloghi (cert J) bottom z a k ν hbefore hstep hinj
    | succ n ih =>
      intro i he k ν hν hbefore
      let : IsProbabilityMeasure ν := hν
      have hi : i < paperCheckpointStop f.natDegree M (T : ℝ) (by omega) := by change i < J; omega
      let q := paperMiddleStartPosition f M R m g0 T (i + 1) P (cert (i + 1))
      have hq : q ≤ (paperScheduleList f.natDegree M g0).length :=
        (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T (i + 1) P (cert (i + 1)))).le
      have hloc := paperMiddleTarget_log_hi f.natDegree m.val (by omega) (T : ℝ) hloglo hloghi i
      have hord := paperMiddleCertificate_before_next f (by omega) M R m hm g0 T i P hM hi hloc
        (cert i) (cert (i + 1))
      have hstart : paperMiddleStartPosition f M R m g0 T i P (cert i) ≤
          paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1 (paperCheckpointTarget f.natDegree T i)
            (paperMiddleIterations M) (cert i).fit) := by
        have h := paperBlockOp_position g0 m hm 1 (paperCheckpointTarget f.natDegree T i)
          (paperMiddleIterations M) (cert i).fit
        dsimp only [paperMiddleStartPosition, paperMiddleStartOp]
        omega
      have hkq : k ≤ q := hbefore.trans (hstart.trans hord.le)
      dsimp only [paperFullTailDeficientFraction]
      apply paperMiddleCertificate_full_terminal_coverage_step f hf hd M R m hm g0 T i hM hacc hi
        hmargin htail hshared hfuture P hP roots hcard hroot e hT hPk hlo hhi hloglo hloghi
        (cert i) (cert (i + 1)) z a k ν hbefore hstep hinj
      dsimp only
      intro c hc
      let νc := (pairedWalkPrefixLaw z (paperScheduleWindow f.natDegree M g0) a k q hkq ν)[|
        pairedWalkTime (paperScheduleWindow f.natDegree M g0) a q ⁻¹' {c}]
      let : IsProbabilityMeasure νc := paperFullTailLaw_cond_next_time_probability z f.natDegree M g0 a
        k q hkq hq ν c hc
      have hcov := ih (i + 1) (by omega) q νc inferInstance le_rfl
      dsimp only [paperFullTailDeficientFraction] at hcov
      have hcount := (div_le_iff₀ hden).mp hcov
      change ((deficientCoordinates ((paperFullTailLaw z f.natDegree M g0 a k ν)[|
        paperFullTailCheckpointTime f.natDegree M g0 a k q hq ⁻¹' {c}])
        (fun p : P × Q => ZMod p.1.val)
        (fun p ω => labelledPrimeResidue P roots e p.1 p.2
          (z (paperFullTailTerminalTime f.natDegree M g0 a k ω)))
        (paperCoverageTau (i + 1)) (paperCheckpointBeta f.natDegree (i + 1))).card : ℝ) ≤ _
      rw [paperFullTailLaw_cond_next_time_deficientCoordinates z f.natDegree M g0 a k q hkq hq ν c
        (fun p : P × Q => ZMod p.1.val) (fun p t => labelledPrimeResidue P roots e p.1 p.2 (z t))]
      simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul] at hcount ⊢
      exact hcount
  intro i hi k ν hν hbefore
  exact descend (J - i) i (by omega) k ν hν hbefore

/-- ONE supplied threshold and ONE actual good-prime batch give coverage at
EVERY paper checkpoint on the actual common terminal law. No block certificate,
high entropy, next-fiber coverage, time/future bound or recurrence is a premise. -/
theorem paperSchedule_constructed_middle_coverage
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∃ hM0 : 2 ≤ M0,
      ∀ M : ℕ, ∀ hMM : M0 ≤ M, ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℕ, 2 ≤ T →
        paperScheduleX f.natDegree m.val ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
        ∃ P : Finset ℕ, ∃ hP : ∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree,
          P.card = paperPrimeCount c T ∧ Disjoint P bad ∧ 0 < P.card ∧
          (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
          let hcard := fun p hp => (hP p hp).2.2.2
          let e := paperPrimeRootLabelEquiv f P hcard
          letI : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).1.ne_zero⟩
          ∀ z : ℕ → Point, ∀ a : A → ℕ, ∀ ν : Measure A, IsProbabilityMeasure ν →
            (∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) → Function.Injective z →
            ∀ i ≤ paperCheckpointStop f.natDegree M (T : ℝ) (by omega),
              paperFullTailDeficientFraction P (primeRootSet f) e z f.natDegree M g0 a 0 ν i ≤ paperCoverageEta i := by
  obtain ⟨c, hc, hs⟩ := paperSchedule_middle_bottom_transfer_ready_batches f hf hd R g0 hg0 hg064
  refine ⟨c, hc, ?_⟩
  intro bad
  obtain ⟨M0, hM02, hacc0, hbase0, hmargin0, htail0, hshared0, hfuture, hbatch⟩ := hs bad
  refine ⟨M0, hM02, ?_⟩
  intro M hM m hm T hT hloglo hloghi
  obtain ⟨P, hsize, hdisjoint, hP, hPk, halpha, cert, bottom⟩ := hbatch M hM m hm T hT hloglo hloghi
  refine ⟨P, hP, hsize, hdisjoint, hPk, halpha, ?_⟩
  dsimp only
  let hcard := fun p hp => (hP p hp).2.2.2
  let e := paperPrimeRootLabelEquiv f P hcard
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).1.ne_zero⟩
  let : Nonempty (Fin f.natDegree) := ⟨⟨0, by omega⟩⟩
  intro z a ν hν hstep hinj i hi
  have h := paperMiddleBottomCertificates_backward_coverage f hf hd M R m hm g0 T
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hfuture M hM) P (fun p hp => (hP p hp).1) (primeRootSet f) hcard
    (fun p hp ρ hρ => (mem_primeRootSet f p (hP p hp).1 ρ).mp hρ) e hT hPk
    (fun p hp => (hP p hp).2.1) (fun p hp => (hP p hp).2.2.1) hloglo hloghi cert bottom z a hstep hinj
  exact h i hi 0 ν hν (Nat.zero_le _)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailDeficientFraction
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleBottomCertificates_full_terminal_base
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleBottomCertificates_backward_coverage

#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_constructed_middle_coverage
