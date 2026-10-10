import Integrations.PaperCoverageParameters435
import Integrations.SingletonCoverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The actual prime/root singleton entropy implies a quantitative coverage
bound on the SAME law, without assuming uniformity of individual marginals. -/
theorem labelledPrime_singleton_few_deficient {Ω Q : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ S p.val)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Point)
    (T : ℕ) (hT : 2 ≤ T) (hPk : 0 < P.card) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (ε τ β : ℝ) (hτ : τ ≤ 3 / 8) (hβ : 0 ≤ β)
    (high : (1 - ε) * primeBatchLogMean P ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e) μ 1 X) :
    ((deficientCoordinates μ (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) τ β).card : ℝ) /
        (P.card * (Fintype.card Q : ℝ)) ≤ 8 * ε * primeBatchLogMean P * (2 * T : ℝ) ^ β := by
  let : Nonempty P := Fintype.card_pos_iff.mp (by simpa only [Fintype.card_coe] using hPk)
  have hmean : coordinateLogMean (fun c : P × Q => ZMod c.1.val) = primeBatchLogMean P := by
    rw [rootResidue_coordinateLogMean]
    simp only [primeBatchLogMean, Fintype.card_coe]
  have hs : 1 ≤ Fintype.card P := by rw [Fintype.card_coe]; omega
  have hh : (1 - ε) * ((1 : ℕ) : ℝ) * coordinateLogMean (fun c : P × Q => ZMod c.1.val) ≤
      labelSubsetJointEntropy μ (fun c : P × Q => ZMod c.1.val)
        (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) 1 := by
    have he : labelSubsetJointEntropy μ (fun c : P × Q => ZMod c.1.val)
        (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) 1 =
        labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e) μ 1 X := rfl
    rw [he, hmean, Nat.cast_one, mul_one]
    exact high
  have hn : (0 : ℝ) < 2 * T := by
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    positivity
  have h := high_entropy_few_deficient_coordinates μ (fun c : P × Q => ZMod c.1.val)
    (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) (fun _ => measurable_of_finite _)
    1 (by omega) hs ε τ β (2 * T) hτ hβ hn
    (fun c => by simp only [ZMod.card]; exact_mod_cast hhi c.1.val c.1.property) hh
  simpa only [hmean, Fintype.card_coe] using h

/-- ONE terminal-base threshold precedes ALL windows, batch values and laws.
The coarse proof compares a cubic with a fixed quadratic; M^20 supplies slack. -/
theorem paperTerminalCoverage_budget_threshold (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M ≥ M0, ∀ (hM1 : 1 ≤ M), ∀ m : ℕ, m ≤ M → ∀ T : ℝ, 2 ≤ T →
      Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m → ∀ L : ℝ, 0 ≤ L →
        L ≤ Real.log (2 * T) →
        8 * Real.exp (-90 * (M : ℝ) ^ 20) * L *
          (2 * T) ^ paperCheckpointBeta d (paperCheckpointStop d M T hM1) <
            paperCoverageEta (paperCheckpointStop d M T hM1) := by
  let b := Real.log (paperScheduleBase d)
  let C := b + 25 + 10 * (100 * (d : ℝ) + 1) ^ 2
  let M0 := Nat.ceil C + 2
  refine ⟨M0, by omega, ?_⟩
  intro M hM hM1 m hm T hT hlog L hL0 hL
  have hMn : 1 ≤ M := by omega
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hMn
  have hMP : (0 : ℝ) < M := by linarith
  have hb : 0 < b := Real.log_pos (paperScheduleBase_gt_one d hd)
  have hCM : C < (M : ℝ) := by
    have hc : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
    have hn : (Nat.ceil C : ℝ) + 2 ≤ M := by exact_mod_cast hM
    linarith
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlogM : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d M :=
    hlog.trans (mul_le_mul_of_nonneg_left (paperScheduleX_mono d hd hm) (by norm_num))
  let J := paperCheckpointStop d M T hMn
  let β := paperCheckpointBeta d J
  have hβP : 0 < β := paperCheckpointBeta_pos d J hd
  have hβ1 : β ≤ 1 := by
    have ha := paperCheckpointBeta_antitone d hd (Nat.zero_le J)
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hz : paperCheckpointBeta d 0 ≤ 1 := by
      norm_num only [paperCheckpointBeta, pow_zero] at *
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact ha.trans hz
  have hstop : β * Real.log T ≤ (M : ℝ) ^ 20 := paperCheckpointStop_spec d M T hMn
  have hj : (J : ℝ) ≤ 100 * d * M := by
    exact_mod_cast paperCheckpointStop_linear_bound d M hd T hMn hlogM
  have hxm : 1 ≤ paperScheduleX d M := one_le_pow₀ (paperScheduleBase_gt_one d hd).le
  have hLL : L ≤ 3 * Real.exp (b * M) := by
    have ht : 0 < T := by linarith
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne'] at hL
    rw [← paperScheduleX_exp d M hd]
    linarith
  have hpow : (2 * T) ^ β ≤ Real.exp ((M : ℝ) ^ 20 + 1) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
    have hx : β * Real.log 2 ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hβP.le]
    nlinarith
  have h24 : (24 : ℝ) ≤ Real.exp 24 := by linarith [Real.add_one_le_exp (24 : ℝ)]
  have herr : 8 * Real.exp (-90 * (M : ℝ) ^ 20) * L * (2 * T) ^ β ≤
      Real.exp (-89 * (M : ℝ) ^ 20 + b * M + 25) := by
    calc
      _ ≤ 24 * (Real.exp (-90 * (M : ℝ) ^ 20) * Real.exp (b * M) * Real.exp ((M : ℝ) ^ 20 + 1)) := by
        have hcost := mul_le_mul_of_nonneg_left hLL
          (show 0 ≤ 8 * Real.exp (-90 * (M : ℝ) ^ 20) from by positivity)
        have hprod := mul_le_mul hcost hpow (Real.rpow_nonneg (by positivity) _)
          (show 0 ≤ 8 * Real.exp (-90 * (M : ℝ) ^ 20) * (3 * Real.exp (b * M)) from by positivity)
        exact hprod.trans_eq (by ring)
      _ = 24 * Real.exp (-89 * (M : ℝ) ^ 20 + b * M + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp 24 * Real.exp (-89 * (M : ℝ) ^ 20 + b * M + 1) :=
        mul_le_mul_of_nonneg_right h24 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hM2 : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hsq : (100 * (d : ℝ) * M + 1) ^ 2 ≤ (100 * (d : ℝ) + 1) ^ 2 * (M : ℝ) ^ 2 := by
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hl : 100 * (d : ℝ) * M + 1 ≤ (100 * (d : ℝ) + 1) * M := by nlinarith
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 100 * d * M + 1) hl
    nlinarith
  have hc : b * M + 25 + 10 * (100 * (d : ℝ) * M + 1) ^ 2 ≤ C * (M : ℝ) ^ 2 := by
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left hM2 hb.le, one_le_pow₀ hMR (n := 2)]
  have hc3 : C * (M : ℝ) ^ 2 < (M : ℝ) ^ 3 := by
    have h := mul_lt_mul_of_pos_right hCM (pow_pos hMP 2)
    nlinarith
  have hp20 : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hMR (by norm_num)
  have hexp : -89 * (M : ℝ) ^ 20 + b * M + 25 <
      -10 * (100 * (d : ℝ) * M + 1) ^ 2 := by
    nlinarith [pow_nonneg hMP.le 20]
  have hjexp : -10 * (100 * (d : ℝ) * M + 1) ^ 2 ≤ -10 * ((J : ℝ) + 1) ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1) (by linarith :
      (J : ℝ) + 1 ≤ 100 * d * M + 1)
    nlinarith
  exact herr.trans_lt ((Real.exp_lt_exp.mpr hexp).trans_le
    ((Real.exp_le_exp.mpr hjexp).trans (paperCoverageEta_exp_lower J)))

def paperTerminalCoverageThreshold (d : ℕ) (hd : 1 ≤ d) : ℕ :=
  Classical.choose (paperTerminalCoverage_budget_threshold d hd)

theorem paperTerminalCoverageThreshold_spec (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ paperTerminalCoverageThreshold d hd ∧
      ∀ M ≥ paperTerminalCoverageThreshold d hd, ∀ (hM1 : 1 ≤ M), ∀ m : ℕ, m ≤ M → ∀ T : ℝ, 2 ≤ T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m → ∀ L : ℝ, 0 ≤ L →
          L ≤ Real.log (2 * T) →
          8 * Real.exp (-90 * (M : ℝ) ^ 20) * L *
            (2 * T) ^ paperCheckpointBeta d (paperCheckpointStop d M T hM1) <
              paperCoverageEta (paperCheckpointStop d M T hM1) :=
  Classical.choose_spec (paperTerminalCoverage_budget_threshold d hd)

/-- The constructed bottom block supplies coverage on the ACTUAL smoothed
tail terminal law, for ANY earlier full-history probability law. -/
theorem paperBottomCertificate_terminal_deficient_budget
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T : ℕ) (hM : 1 ≤ M)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (cert : PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
      (paperBottomIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 2
      (paperBottomTarget f.natDegree m.val) 0 (by have := cert.fit; omega)))
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (τ β : ℝ) (hτ : τ ≤ 3 / 8) (hβ : 0 ≤ β) :
    let μ := pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))
    let X := fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)
    ((deficientCoordinates μ (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) τ β).card : ℝ) /
        (P.card * (Fintype.card Q : ℝ)) ≤ 8 * Real.exp (-90 * (M : ℝ) ^ 20) * primeBatchLogMean P * (2 * T : ℝ) ^ β := by
  dsimp only
  let : MeasurableSpace Q := ⊤
  let : MeasurableSingletonClass Q := inferInstance
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) :=
    ⟨(terminalSmoothingLength_pos _).ne'⟩
  let μ := pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))
  let X := fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)
  have high := paperBottomCertificate_terminal_singleton_entropy f hf hd M R m hm g0 T hM
    P hP S hcard hroot e hT hPk hlo hhi cert z a k0 ν hbefore hstep hinj
  exact labelledPrime_singleton_few_deficient P S e μ X T hT hPk hhi
    (Real.exp (-90 * (M : ℝ) ^ 20)) τ β hτ hβ high

/-- The paper's terminal base case: the ACTUAL deficient-coordinate
fraction is strictly below eta_J. The common threshold is independent of the
walk, every source and starting law, the window and prime/root enumeration. -/
theorem paperBottomCertificate_terminal_coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 : ℝ) (T : ℕ) (hM : 1 ≤ M)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (cert : PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
      (paperBottomIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 2
      (paperBottomTarget f.natDegree m.val) 0 (by have := cert.fit; omega)))
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (hlog : Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val)
    (hbase : paperTerminalCoverageThreshold f.natDegree (by omega) ≤ M) :
    let J := paperCheckpointStop f.natDegree M (T : ℝ) hM
    let τ := paperCoverageTau J
    let β := paperCheckpointBeta f.natDegree J
    let μ := pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))
    let X := fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0
      ((paperScheduleList f.natDegree M g0).length - k0)
      (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)
    ((deficientCoordinates μ (fun c : P × Q => ZMod c.1.val)
      (fun c ω => labelledPrimeResidue P S e c.1 c.2 (X ω)) τ β).card : ℝ) /
        (P.card * (Fintype.card Q : ℝ)) < paperCoverageEta J := by
  dsimp only
  let J := paperCheckpointStop f.natDegree M (T : ℝ) hM
  have hβ := (paperCheckpointBeta_pos f.natDegree J (by omega)).le
  have hτ := (paperCoverageTau_bounds J).2.le
  have h := paperBottomCertificate_terminal_deficient_budget f hf hd M R m hm g0 T hM
    P hP S hcard hroot e hT hPk hlo hhi cert z a k0 ν hbefore hstep hinj
    (paperCoverageTau J) (paperCheckpointBeta f.natDegree J) hτ hβ
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hb := (paperTerminalCoverageThreshold_spec f.natDegree (by omega)).2 M hbase hM
    m.val (by omega) (T : ℝ) (by exact_mod_cast hT) hlog (primeBatchLogMean P) hL.1.le
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hL.2.2.1)
  exact h.trans_lt hb

/-- Add the terminal-base coverage threshold to the SAME uniform
middle/bottom prime-batch supplier, before all growing families and laws. -/
theorem paperSchedule_middle_bottom_coverage_ready_batches (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∃ M0 : ℕ, 2 ≤ M0 ∧ paperMiddleAccuracyThreshold ≤ M0 ∧
      paperTerminalCoverageThreshold f.natDegree (by omega) ≤ M0 ∧ ∀ M ≥ M0,
      ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℕ, 2 ≤ T →
        paperScheduleX f.natDegree m.val ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
        ∃ P : Finset ℕ, P.card = paperPrimeCount c T ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
          0 < P.card ∧ (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
          (∀ i : ℕ, PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
            (paperMiddleIterations M) P) ∧
          PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
            (paperBottomIterations M) P := by
  obtain ⟨c, hc, hs⟩ := paperSchedule_middle_bottom_ready_batches f hf hd R g0 hg0 hg064
  refine ⟨c, hc, ?_⟩
  intro bad
  obtain ⟨M0, hM02, hacc, hM0⟩ := hs bad
  let C0 := paperTerminalCoverageThreshold f.natDegree (by omega)
  refine ⟨M0 + C0, by omega, by omega, by omega, ?_⟩
  intro M hM
  exact hM0 M (by omega)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.labelledPrime_singleton_few_deficient
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalCoverage_budget_threshold
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalCoverageThreshold
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalCoverageThreshold_spec
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomCertificate_terminal_deficient_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomCertificate_terminal_coverage
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_middle_bottom_coverage_ready_batches
