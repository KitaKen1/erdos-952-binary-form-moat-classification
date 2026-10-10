import Integrations.PaperCheckpointBatches435
import Integrations.PaperTailBlockEntropy435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A universal accuracy threshold is chosen before every polynomial/batch. -/
def paperMiddleAccuracyThreshold : ℕ := Classical.choose paperMiddle_preserved_deficit_eventually

theorem paperMiddleAccuracyThreshold_spec (M : ℕ) (hM : paperMiddleAccuracyThreshold ≤ M) :
    90 * paperScheduleMiddleG M + (1 / 2 : ℝ) ^ paperMiddleIterations M ≤
      Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) :=
  Classical.choose_spec paperMiddle_preserved_deficit_eventually M hM

/-- ONE full threshold includes all batch/block inputs, M>=2 and middle accuracy. -/
theorem paperSchedule_middle_bottom_ready_batches (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∃ M0 : ℕ, 2 ≤ M0 ∧ paperMiddleAccuracyThreshold ≤ M0 ∧ ∀ M ≥ M0,
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
  obtain ⟨c, hc, hs⟩ := paperSchedule_middle_bottom_batches f hf hd R g0 hg0 hg064
  refine ⟨c, hc, ?_⟩
  intro bad
  obtain ⟨M0, hM0⟩ := hs bad
  refine ⟨M0 + 2 + paperMiddleAccuracyThreshold, by omega, by omega, ?_⟩
  intro M hM
  exact hM0 M (by omega)

/-- Constructed record-size inputs discharge the true-mean premise in the
previous exponential rank-mass bound. No additional mean-fit assumption. -/
theorem paperMiddleCertificate_record_mass (f : Polynomial ℤ) (M R : ℕ)
    (m : Fin (M + 1)) (g0 : ℝ) (T i : ℕ) (P : Finset ℕ) (hM : 1 ≤ M)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hVhi : Real.log (paperCheckpointTarget f.natDegree T i) ≤ paperBandHi f.natDegree m.val 1)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P) :
    Real.exp (paperCheckpointRadius f.natDegree i * Real.log T - 4 * (M : ℝ) ^ 6) / 2 ≤
      (paperInputRank (paperBlockScale f.natDegree M m.val g0 1 (paperCheckpointTarget f.natDegree T i)
        (paperMiddleIterations M)) (primeBatchLogMean P) : ℝ) * primeBatchLogMean P := by
  let U := paperBlockScale f.natDegree M m.val g0 1 (paperCheckpointTarget f.natDegree T i)
    (paperMiddleIterations M)
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  have hU : 0 < U := paperBandScale_pos _ _ (Real.exp_pos _) cert.inputs.g_pos _
  have hc := paper_terminal_relative_cost f R U (primeBatchLogMean P) (paperBandG M g0 1)
    hU hL hL2 cert.inputs.g_pos cert.inputs.g_small cert.record_size
  have hgmid : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  have hg1 : paperScheduleMiddleG M < 1 := by
    have h := cert.inputs.g_small
    rw [hgmid] at h
    linarith
  have hb : paperCheckpointRadius f.natDegree i * Real.log T - 4 * (M : ℝ) ^ 6 < Real.log U := by
    simpa only [U, paperBlockScale, hgmid] using
      paperCheckpoint_middle_record_log f.natDegree M m.val T i hM hVhi hg1
  have he := Real.exp_lt_exp.mpr hb
  rw [Real.exp_log hU] at he
  linarith [hc.2.1]

/-- Certified middle records lie strictly before the certified next checkpoint. -/
theorem paperMiddleCertificate_before_next (f : Polynomial ℤ) (hd : 1 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 : ℝ) (T i : ℕ) (P : Finset ℕ) (hM : 2 ≤ M)
    (hi : i < paperCheckpointStop f.natDegree M T (by omega))
    (hVhi : Real.log (paperCheckpointTarget f.natDegree T i) ≤ paperBandHi f.natDegree m.val 1)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (next : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T (i + 1))
      (paperMiddleIterations M) P) :
    paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) cert.fit) <
      paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1 (paperCheckpointTarget f.natDegree T (i + 1))
        0 (by have := next.fit; omega)) := by
  have hgb : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  have hgap := paperCheckpoint_middle_entry_gap f.natDegree M m.val hd T hM i hi hVhi
  have hg : paperBandEntry (paperBandHi f.natDegree m.val 1) (paperBandG M g0 1)
      (paperCheckpointTarget f.natDegree T i) + paperMiddleIterations M <
      paperBandEntry (paperBandHi f.natDegree m.val 1) (paperBandG M g0 1)
        (paperCheckpointTarget f.natDegree T (i + 1)) := by simpa only [hgb] using hgap
  have hp := paperOpPosition_band_strict m hm 1 _ _ cert.fit (by have := next.fit; omega) hg
  simpa only [paperBlockOp, Nat.add_zero] using hp

/-- Every constructed middle checkpoint supplies the PAPER exponentially
accurate joint-entropy input on the actual next-checkpoint continuation law. -/
theorem paperMiddleCertificate_next_entropy
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 : ℝ) (T i : ℕ) (hM : 2 ≤ M) (hacc : paperMiddleAccuracyThreshold ≤ M)
    (hi : i < paperCheckpointStop f.natDegree M T (by omega))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hVhi : Real.log (paperCheckpointTarget f.natDegree T i) ≤ paperBandHi f.natDegree m.val 1)
    (cert : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M) P)
    (next : PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T (i + 1))
      (paperMiddleIterations M) P)
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1
      (paperCheckpointTarget f.natDegree T i) 0 (by have := cert.fit; omega)))
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let r := paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1
      (paperCheckpointTarget f.natDegree T (i + 1)) 0 (by have := next.fit; omega))
    let q := paperInputRank (paperBlockScale f.natDegree M m.val g0 1 (paperCheckpointTarget f.natDegree T i)
      (paperMiddleIterations M)) (primeBatchLogMean P)
    1 - Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (r - k0)) q
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (r - k0)) ω)) /
        ((q : ℝ) * primeBatchLogMean P) := by
  dsimp only
  let r := paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 1
    (paperCheckpointTarget f.natDegree T (i + 1)) 0 (by have := next.fit; omega))
  have hrecord := paperMiddleCertificate_before_next f (by omega) M R m hm g0 T i P hM hi hVhi cert next
  have hend : r ≤ (paperScheduleList f.natDegree M g0).length :=
    (paperOpPosition_lt _ (paperBlockOp_mem g0 m hm 1 _ 0 (by have := next.fit; omega))).le
  have ht := paperBlockCertificate_tail_later_entropy f hf hd M R m hm g0 1
    (paperCheckpointTarget f.natDegree T i) (paperMiddleIterations M) T
    (by change 1 ≤ M ^ 3; exact one_le_pow₀ (show 1 ≤ M by omega))
    P hP S hcard hroot e hT hPk hlo hhi cert z a k0 r ν hbefore hrecord.le hend hstep hinj
  have hgb : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  simp only [hgb] at ht
  linarith [paperMiddleAccuracyThreshold_spec M hacc]

/-- The singleton mean dominates entropy per coordinate. Forward increments
suffice; no separate full concavity library is needed. -/
theorem labelledPointEntropyMean_div_le_one {Ω ι Q : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) :
    labelledPointEntropyMean K F μ s X / s ≤ labelledPointEntropyMean K F μ 1 X := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hz : s = 0
    · subst s; simp
    · have hsP : 0 < s := by omega
      have hsR : (0 : ℝ) < s := by exact_mod_cast hsP
      have hs1R : (0 : ℝ) < (s + 1 : ℕ) := by exact_mod_cast (by omega : 0 < s + 1)
      have hb := labelledSubsetEntropy_forward_increment_le K μ
        (fun i q ω => F i q (X ω)) (fun _ _ => measurable_of_finite _) s hsP (by omega)
      change labelledPointEntropyMean K F μ (s + 1) X - labelledPointEntropyMean K F μ s X ≤
        labelledPointEntropyMean K F μ s X / s at hb
      have hm := (le_div_iff₀ hsR).mp hb
      apply le_trans _ (ih (by omega) (by omega))
      apply (div_le_div_iff₀ hs1R hsR).mpr
      push_cast
      nlinarith

/-- A constructed bottom block gives the manuscript's exp(-90M^20)
SINGLETON mean at the actual smoothed tail terminal, for every earlier law. -/
theorem paperBottomCertificate_terminal_singleton_entropy
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
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    (1 - Real.exp (-90 * (M : ℝ) ^ 20)) * primeBatchLogMean P ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν
          ((paperScheduleList f.natDegree M g0).length - k0)
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))) 1
        (fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0
          ((paperScheduleList f.natDegree M g0).length - k0)
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)) := by
  let L := primeBatchLogMean P
  let U := paperBlockScale f.natDegree M m.val g0 2 (paperBottomTarget f.natDegree m.val)
    (paperBottomIterations M)
  let q := paperInputRank U L
  let μ := pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν
    ((paperScheduleList f.natDegree M g0).length - k0)
    (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))
  let X := fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0
    ((paperScheduleList f.natDegree M g0).length - k0)
    (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) :=
    ⟨(terminalSmoothingLength_pos _).ne'⟩
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ L :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  have hl : 1 ≤ paperBottomIterations M := by
    unfold paperBottomIterations
    have hp : 1 ≤ M ^ 20 := one_le_pow₀ hM
    omega
  have hqi := paperInventoryBlock_record_inventory f (R + 1) M m.val g0 2
    (paperBottomTarget f.natDegree m.val) (paperBottomIterations M) P hl hL hL2 cert.inputs
  have ho := paperBlockOp_mem g0 m hm 2 (paperBottomTarget f.natDegree m.val) (paperBottomIterations M) cert.fit
  have hr := (paperOpPosition_lt _ ho).le
  have high := paperBlockCertificate_tail_terminal_entropy f hf hd M R m hm g0 2
    (paperBottomTarget f.natDegree m.val) (paperBottomIterations M) T hl P hP S hcard hroot e
    hT hPk hlo hhi cert z a k0 (paperScheduleList f.natDegree M g0).length ν hbefore hr le_rfl hstep hinj
  have hh : 1 - Real.exp (-90 * (M : ℝ) ^ 20) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e) μ q X / ((q : ℝ) * L) := by
    have hd0 := paperBottom_preserved_deficit_bound M hM
    change 1 - 90 * paperScheduleMinG M - (1 / 2 : ℝ) ^ paperBottomIterations M ≤ _ at high
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqi.1
  have hmass : 0 < (q : ℝ) * L := mul_pos hqR hL
  have hmul := (le_div_iff₀ hmass).mp hh
  have hnorm : (1 - Real.exp (-90 * (M : ℝ) ^ 20)) * L ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e) μ q X / q := by
    apply (le_div_iff₀ hqR).mpr
    nlinarith
  exact hnorm.trans (labelledPointEntropyMean_div_le_one (fun p : P => ZMod p.val)
    (labelledPrimeResidue P S e) μ X q hqi.1 (by simpa only [Fintype.card_coe] using (show q ≤ P.card from hqi.2)))

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleAccuracyThreshold
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleAccuracyThreshold_spec
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCertificate_record_mass
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCertificate_before_next
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCertificate_next_entropy
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointEntropyMean_div_le_one
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomCertificate_terminal_singleton_entropy

#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_middle_bottom_ready_batches
