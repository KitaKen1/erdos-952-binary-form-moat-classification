import Integrations.PaperTerminalBlock435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- Canonical root alphabets really admit the degree-many label enumeration
used below; the root-enumeration quantifier is not an existence shortcut. -/
def paperPrimeRootLabelEquiv (f : Polynomial ℤ) (P : Finset ℕ)
    (hcard : ∀ p ∈ P, (primeRootSet f p).card = f.natDegree) (p : P) :
    Fin f.natDegree ≃ primeRootSet f p.val :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (hcard p.val p.property).symm)

/-- The last actual transition supplies the recording rank's inventory;
there is no additional prime-capacity assumption at the recording checkpoint. -/
theorem paperInventoryBlock_record_inventory (f : Polynomial ℤ) (D M m : ℕ)
    (g0 : ℝ) (band : Fin 3) (V : ℝ) (l : ℕ) (P : Finset ℕ)
    (hl : 1 ≤ l) (hL : 0 < primeBatchLogMean P) (hL2 : Real.log 2 ≤ primeBatchLogMean P)
    (hinputs : PaperInventoryBlockInputs f D M m g0 band V l P) :
    0 < paperInputRank
      (paperBandScale (Real.exp (paperBandHi f.natDegree m band)) (paperBandG M g0 band)
        (paperBandEntry (paperBandHi f.natDegree m band) (paperBandG M g0 band) V + l))
      (primeBatchLogMean P) ∧
    paperInputRank
      (paperBandScale (Real.exp (paperBandHi f.natDegree m band)) (paperBandG M g0 band)
        (paperBandEntry (paperBandHi f.natDegree m band) (paperBandG M g0 band) V + l))
      (primeBatchLogMean P) ≤ P.card := by
  let g := paperBandG M g0 band
  let n := paperBandEntry (paperBandHi f.natDegree m band) g V
  let U := paperBandScale (Real.exp (paperBandHi f.natDegree m band)) g (n + (l - 1))
  have hs := paperEnrichment_size_inputs f D U (primeBatchLogMean P) g
    (paperBandScale_pos _ _ (Real.exp_pos _) hinputs.g_pos _) hL hL2 hinputs.g_pos
    (by linarith [hinputs.g_small]) (hinputs.size (l - 1) (by omega))
  have hr := paperRank_pair_bounds U (primeBatchLogMean P) g
    (paperBandScale_pos _ _ (Real.exp_pos _) hinputs.g_pos _) hL
    hinputs.g_pos hinputs.g_small hs.2.1
  have he : n + l = (n + (l - 1)) + 1 := by omega
  change 0 < paperInputRank (paperBandScale (Real.exp (paperBandHi f.natDegree m band)) g (n + l))
    (primeBatchLogMean P) ∧ _
  rw [he, paperBandScale_rank_match]
  exact ⟨hr.1, hr.2.1.le.trans (hinputs.inventory (l - 1) (by omega))⟩

/-- A true dyadic mean retains the correct scale while admitting the coarse
two-log upper envelope required by the common all-operation threshold. -/
theorem primeBatchLogMean_le_twolog (P : Finset ℕ) (T : ℕ) (hT : 2 ≤ T)
    (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T) :
    primeBatchLogMean P ≤ 2 * Real.log (T : ℝ) := by
  have h := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.2.1
  have hlog2 : Real.log 2 ≤ Real.log (T : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num)
    (by exact_mod_cast (by omega : T ≠ 0))] at h
  linarith

/-- ALL admissible top batches have high entropy on ONE actual terminal law.
c,a0 precede the block length and finite exclusion; the common M threshold
precedes every batch, finite source, walk, starting law and root enumeration. -/
theorem paperSchedule_top_terminal_entropy (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, 1 ≤ l → ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∀ M ≥ M0,
        ∀ m : ℕ, (M + 1) / 2 ≤ m → m ≤ M →
          ∀ T : ℕ, 2 ≤ T → paperScheduleX f.natDegree m ≤ Real.log T →
            Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m →
            ∃ P : Finset ℕ, Disjoint P bad ∧
              (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
              0 < P.card ∧ (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
              let U := paperBandScale (Real.exp (paperBandHi f.natDegree m 0)) g0
                (paperBandEntry (paperBandHi f.natDegree m 0) g0 (a0 * T) + l)
              let q := paperInputRank U (primeBatchLogMean P)
              0 < q ∧ q ≤ P.card ∧
              (((g0 ^ 2) ^ (l + 1) * a0) / 2) * T ≤ (q : ℝ) * primeBatchLogMean P ∧
              ∀ (A Q : Type*) [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
                [Fintype Q] [Nonempty Q] [∀ p : P, NeZero p.val]
                (e : ∀ p : P, Q ≃ primeRootSet f p.val)
                (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (a : A → ℕ),
                (∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) → Function.Injective z →
                  1 - 90 * g0 - (1 / 2 : ℝ) ^ l ≤
                    labelledPointEntropyMean (fun p : P => ZMod p.val)
                      (labelledPrimeResidue P (primeRootSet f) e)
                      (paperTerminalLaw z μ a f.natDegree M g0) q
                      (fun ω => z (paperTerminalTime a f.natDegree M g0 ω)) /
                      ((q : ℝ) * primeBatchLogMean P) := by
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hsupply⟩ :=
    paperSchedule_top_inventory_blocks f hf hd (R + 1) g0 hg0 hg064
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l hl bad
  obtain ⟨Mbatch, hbatch⟩ := hsupply l bad
  obtain ⟨Mroom, hroom⟩ := paperSchedule_top_block_fits f.natDegree (by omega) a0 g0
    ha0 ha01 hg0 (by linarith) l
  obtain ⟨Msize, hsize⟩ := paperSchedule_uniform_size_threshold f (R + 1) (by omega) g0 hg0
  obtain ⟨Mshift, hshift⟩ := paperSchedule_uniform_future_shift f.natDegree (by omega) g0 hg0 (by linarith)
  obtain ⟨Mmass, hmass⟩ := paperSchedule_top_record_mass f.natDegree (by omega) a0 g0
    ha0 ha01 hg0 (by linarith) l
  refine ⟨max Mbatch (max Mroom (max Msize (max Mshift Mmass))), ?_⟩
  intro M hM m hmlo hmhi T hT hTlo hThi
  have hb : Mbatch ≤ M := (le_max_left _ _).trans hM
  have hr : Mroom ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hs : Msize ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have ht : Mshift ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM)))
  have hma : Mmass ≤ M := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM)))
  obtain ⟨P, hbad, hP, hPk, hAlpha, hinputs⟩ := hbatch M hb m hmlo hmhi T hT hTlo hThi
  have hlo : ∀ p ∈ P, T ≤ p := fun p hp => (hP p hp).2.1
  have hhi : ∀ p ∈ P, p ≤ 2 * T := fun p hp => (hP p hp).2.2.1
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans
      (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).2.1
  have hfit := hroom M hr m hmlo T hT hTlo hThi
  let n := paperBandEntry (paperBandHi f.natDegree m 0) g0 (a0 * T)
  let U := paperBandScale (Real.exp (paperBandHi f.natDegree m 0)) g0 (n + l)
  have hn : n + l < paperBandOperationCount f.natDegree M m g0 0 := hfit
  let mf : Fin (M + 1) := ⟨m, by omega⟩
  let o : PaperScheduleOp f.natDegree M g0 := ⟨mf, 0, ⟨n + l, hn⟩⟩
  have ho : o ∈ paperScheduledOps f.natDegree M g0 := by
    simpa only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and] using hmlo
  let k : Fin (paperScheduleList f.natDegree M g0).length := ⟨paperOpPosition o, paperOpPosition_lt o ho⟩
  have hget : (paperScheduleList f.natDegree M g0).get k = o := paperOpPosition_get o ho
  have hsrecord : paperEnrichmentSizeConstant f (R + 1) * primeBatchLogMean P ≤ g0 ^ 10 * U :=
    hsize M hs (paperOpStage o ho (by omega) hg0 (by change g0 < 1; linarith) T (primeBatchLogMean P)
      (by exact_mod_cast (by omega : 1 < T)) hThi
      (primeBatchLogMean_le_twolog P T hT hPk hlo hhi))
  have hqi := paperInventoryBlock_record_inventory f (R + 1) M m g0 0 (a0 * T) l P hl hL hL2 hinputs
  refine ⟨P, hbad, hP, hPk, hAlpha, hqi.1, hqi.2,
    hmass M hma m hmlo T hT hTlo hThi P hPk hlo hhi, ?_⟩
  intro A Q _ _ _ _ _ _ e z μ _ a hstep hinj
  have he := paperInventoryBlock_global_enrichment f hf hd (R + 1) M mf hmlo g0 0 (a0 * T) l T
    (by simpa only [paperBandG, ↓reduceIte] using hn) P
    (fun p hp => (hP p hp).1) (primeRootSet f) (fun p hp => (hP p hp).2.2.2)
    (fun p hp ρ hρ => (mem_primeRootSet f p (hP p hp).1 ρ).mp hρ) e hT hPk hlo hhi hinputs
    z μ a (sqDist_walk_coordinate_steps z R hstep) hinj
  have hg_top : paperBandG M g0 (0 : Fin 3) = g0 := by simp [paperBandG]
  simp only [hg_top] at he
  have hpos := paperOpPosition_block (d := f.natDegree) (g0 := g0) mf hmlo 0 n l hn
  have hh : 1 - (80 * g0 + (1 / 2 : ℝ) ^ l) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P (primeRootSet f) e)
        (pairedWalkLaw z (paperScheduleWindow f.natDegree M g0) μ a k.val)
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a k.val ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
    let H := fun j =>
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P (primeRootSet f) e)
        (pairedWalkLaw z (paperScheduleWindow f.natDegree M g0) μ a j)
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a j ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)
    change 1 - (80 * g0 + (1 / 2 : ℝ) ^ l) ≤ H (paperOpPosition o)
    change paperOpPosition o = _ at hpos
    rw [hpos]
    convert he using 1 <;> first | rfl | ring
  have hterm := paperCheckpoint_labelledPoint_normalized_terminal f P (primeRootSet f) e
    z μ a M R g0 hstep k U g0 (80 * g0 + (1 / 2 : ℝ) ^ l)
    (paperOp_pos o hg0) hg0 hg064 hL hL2
    (by rw [hget]; exact ⟨rfl, rfl⟩) hsrecord hqi.2
    (by rw [hget]; exact hshift M ht o ho) hh
  convert hterm using 1; ring

/-- Choose fixed accuracy BEFORE M, allowing the terminal preservation cost. -/
theorem paperTerminal_fixed_accuracy (ε : ℝ) (hε : 0 < ε) :
    ∃ l0 : ℕ, 1 ≤ l0 ∧ ∃ g0 : ℝ, 0 < g0 ∧ g0 < 1 / 64 ∧
      ∀ l ≥ l0, ∀ g : ℝ, 0 ≤ g → g ≤ g0 → 90 * g + (1 / 2 : ℝ) ^ l ≤ ε := by
  obtain ⟨l0, g0, hg0, hg064, hacc⟩ := paperEnrichment_fixed_accuracy (ε / 2) (by positivity)
  refine ⟨max 1 l0, le_max_left _ _, g0, hg0, hg064, ?_⟩
  intro l hl g hg hgg
  have h := hacc l ((le_max_right _ _).trans hl) g hg hgg
  have hp : 0 ≤ (1 / 2 : ℝ) ^ l := by positivity
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperInventoryBlock_record_inventory
#print axioms BinaryFormMoat.GeometryIntegration.primeBatchLogMean_le_twolog
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_top_terminal_entropy
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminal_fixed_accuracy
#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeRootLabelEquiv
