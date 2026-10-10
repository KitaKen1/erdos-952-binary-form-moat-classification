import Integrations.PaperBlockCertificate435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Full block certificates yield high entropy at ANY later actual checkpoint
under ANY probability law at ANY earlier checkpoint. Enrichment is derived. -/
theorem paperBlockCertificate_tail_later_entropy
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 : ℝ) (band : Fin 3) (V : ℝ) (l T : ℕ) (hl : 1 ≤ l)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (cert : PaperBlockCertificate f R M m g0 band V l P)
    (z : ℕ → Point) (a : A → ℕ) (k0 r : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V 0 (by have := cert.fit; omega)))
    (hrecord : paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V l cert.fit) ≤ r)
    (hend : r ≤ (paperScheduleList f.natDegree M g0).length)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let U := paperBlockScale f.natDegree M m.val g0 band V l
    let q := paperInputRank U (primeBatchLogMean P)
    1 - 90 * paperBandG M g0 band - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (r - k0)) q
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (r - k0)) ω)) /
        ((q : ℝ) * primeBatchLogMean P) := by
  dsimp only
  let g := paperBandG M g0 band
  let U := paperBlockScale f.natDegree M m.val g0 band V l
  let o := paperBlockOp (d := f.natDegree) g0 m band V l cert.fit
  let k := paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V 0 (by have := cert.fit; omega))
  let kr := paperOpPosition o
  have hpos : kr = k + l := paperBlockOp_position g0 m hm band V l cert.fit
  have hb : k0 ≤ k := hbefore
  have hkr_le : kr ≤ r := hrecord
  have hkr : k0 ≤ kr := by omega
  have hr : k0 ≤ r := hkr.trans hrecord
  have hom := paperBlockOp_mem g0 m hm band V l cert.fit
  have hopr : kr < (paperScheduleList f.natDegree M g0).length := paperOpPosition_lt o hom
  have hkrec : k0 + (kr - k0) = kr := by omega
  have hget : (paperScheduleList f.natDegree M g0).get ⟨k0 + (kr - k0), by omega⟩ = o := by
    simpa only [hkrec] using paperOpPosition_get o hom
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  have hqi := paperInventoryBlock_record_inventory f (R + 1) M m.val g0 band V l P hl hL hL2 cert.inputs
  have high := paperInventoryBlock_tail_enrichment f hf hd (R + 1) M m hm g0 band V l T cert.fit
    P hP S hcard hroot e hT hPk hlo hhi cert.inputs z a k0 ν hbefore
    (sqDist_walk_coordinate_steps z R hstep) hinj
  have hh : 1 - (80 * g + (1 / 2 : ℝ) ^ l) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (kr - k0))
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (kr - k0)) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
    have heq : k - k0 + l = kr - k0 := by omega
    change 1 - 80 * g - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (k - k0 + l))
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (k - k0 + l)) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) at high
    rw [heq] at high
    convert high using 1; ring
  have ht := paperTailCheckpoint_labelledPoint_normalized_later f P S e z a M R g0 hstep k0 ν
    (r - k0) (kr - k0) (by omega) (by omega) (by omega) U g
    (80 * g + (1 / 2 : ℝ) ^ l) (paperBandScale_pos _ _ (Real.exp_pos _) cert.inputs.g_pos _)
    cert.inputs.g_pos cert.inputs.g_small hL hL2
    (by rw [hget]; exact ⟨rfl, rfl⟩) cert.record_size hqi.2
    (by rw [hget]; exact cert.future_log) hh
  convert ht using 1; ring

/-- The same derived block entropy transfers to a remaining-schedule terminal
law with its actual independent common smoothing offset. -/
theorem paperBlockCertificate_tail_terminal_entropy
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (M R : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 : ℝ) (band : Fin 3) (V : ℝ) (l T : ℕ) (hl : 1 ≤ l)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, Q ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (cert : PaperBlockCertificate f R M m g0 band V l P)
    (z : ℕ → Point) (a : A → ℕ) (k0 r : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V 0 (by have := cert.fit; omega)))
    (hrecord : paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V l cert.fit) ≤ r)
    (hend : r ≤ (paperScheduleList f.natDegree M g0).length)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let U := paperBlockScale f.natDegree M m.val g0 band V l
    let q := paperInputRank U (primeBatchLogMean P)
    1 - 90 * paperBandG M g0 band - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (r - k0)
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))) q
        (fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k0 (r - k0)
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)) /
        ((q : ℝ) * primeBatchLogMean P) := by
  dsimp only
  let g := paperBandG M g0 band
  let U := paperBlockScale f.natDegree M m.val g0 band V l
  let o := paperBlockOp (d := f.natDegree) g0 m band V l cert.fit
  let k := paperOpPosition (paperBlockOp (d := f.natDegree) g0 m band V 0 (by have := cert.fit; omega))
  let kr := paperOpPosition o
  have hpos : kr = k + l := paperBlockOp_position g0 m hm band V l cert.fit
  have hb : k0 ≤ k := hbefore
  have hkr_le : kr ≤ r := hrecord
  have hkr : k0 ≤ kr := by omega
  have hom := paperBlockOp_mem g0 m hm band V l cert.fit
  have hopr : kr < (paperScheduleList f.natDegree M g0).length := paperOpPosition_lt o hom
  have hkrec : k0 + (kr - k0) = kr := by omega
  have hget : (paperScheduleList f.natDegree M g0).get ⟨k0 + (kr - k0), by omega⟩ = o := by
    simpa only [hkrec] using paperOpPosition_get o hom
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  have hqi := paperInventoryBlock_record_inventory f (R + 1) M m.val g0 band V l P hl hL hL2 cert.inputs
  have high := paperInventoryBlock_tail_enrichment f hf hd (R + 1) M m hm g0 band V l T cert.fit
    P hP S hcard hroot e hT hPk hlo hhi cert.inputs z a k0 ν hbefore
    (sqDist_walk_coordinate_steps z R hstep) hinj
  have hh : 1 - (80 * g + (1 / 2 : ℝ) ^ l) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (kr - k0))
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (kr - k0)) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
    have heq : k - k0 + l = kr - k0 := by omega
    change 1 - 80 * g - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (k - k0 + l))
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (k - k0 + l)) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) at high
    rw [heq] at high
    convert high using 1; ring
  have ht := paperTailCheckpoint_labelledPoint_normalized_terminal f P S e z a M R g0 hstep k0 ν
    (r - k0) (kr - k0) (by omega) (by omega) (by omega) U g
    (80 * g + (1 / 2 : ℝ) ^ l) (paperBandScale_pos _ _ (Real.exp_pos _) cert.inputs.g_pos _)
    cert.inputs.g_pos cert.inputs.g_small hL hL2
    (by rw [hget]; exact ⟨rfl, rfl⟩) cert.record_size hqi.2
    (by rw [hget]; exact cert.future_log) hh
  convert ht using 1; ring

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockCertificate_tail_later_entropy
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockCertificate_tail_terminal_entropy
