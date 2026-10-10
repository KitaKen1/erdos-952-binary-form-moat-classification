import Integrations.PaperPrimeInventory435
import Integrations.PaperBandEntry435
import Integrations.PaperBandRoom435
import Integrations.PaperScheduleOperations435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- Actual scheduled ordinals of one enrichment block, with every scalar
size and input-inventory premise derived at the common threshold. -/
structure PaperInventoryBlockInputs (f : Polynomial ℤ) (D M m : ℕ) (g0 : ℝ)
    (b : Fin 3) (V : ℝ) (l : ℕ) (P : Finset ℕ) : Prop where
  g_pos : 0 < paperBandG M g0 b
  g_small : paperBandG M g0 b < 1 / 64
  size : ∀ j < l, paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤
    (paperBandG M g0 b) ^ 10 * paperBandScale (Real.exp (paperBandHi f.natDegree m b))
      (paperBandG M g0 b) (paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + j)
  inventory : ∀ j < l, paperInputRank
    (paperBandScale (Real.exp (paperBandHi f.natDegree m b)) (paperBandG M g0 b)
      (paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + j))
    (primeBatchLogMean P) ≤ P.card

/-- ONE threshold, independent of the batch, source law and walk, supplies all
block inputs from actual band membership and the constructed prime capacity. -/
theorem paperSchedule_inventory_block_threshold (f : Polynomial ℤ) (D : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m → m ≤ M →
      ∀ (b : Fin 3) (V c : ℝ) (l T : ℕ) (P : Finset ℕ),
        0 < V → Real.log V ≤ paperBandHi f.natDegree m b →
        paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + l <
          paperBandOperationCount f.natDegree M m g0 b →
        V ≤ (c / 2) * T → 2 ≤ T → 0 < P.card →
        (∀ p ∈ P, T ≤ p) → (∀ p ∈ P, p ≤ 2 * T) →
        (c / 2) * ((T : ℝ) / Real.log T) ≤ (P.card : ℝ) →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m →
        PaperInventoryBlockInputs f D M m g0 b V l P := by
  obtain ⟨Msize, hsize⟩ := paperSchedule_uniform_enrichment_threshold f D hd g0 hg0 hg064
  have hsmall := tendsto_paperScheduleMiddleG_zero.eventually (gt_mem_nhds hg0)
  apply Eventually.exists_forall_of_atTop
  filter_upwards [hsmall, eventually_ge_atTop Msize, eventually_ge_atTop (1 : ℕ)] with M hsmall hM hM1
  intro m hmlo hmhi b V c l T P hV hVhi hfit hscale hT hPk hlo hhi hcap hlogT
  have hg := paperBandG_bounds M g0 hM1 hg0 hsmall.le b
  have hg1 : paperBandG M g0 b < 1 := hg.2.2.trans_lt (by linarith)
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hmean : primeBatchLogMean P ≤ 2 * Real.log (T : ℝ) := by
    have hlog2 : Real.log 2 ≤ Real.log (T : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have hTP : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    have he : Real.log (2 * T : ℕ) = Real.log 2 + Real.log (T : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hTP.ne']
    rw [he] at hL
    linarith
  have hstage (j : ℕ) (hj : j ≤ l) :
      ∃ s : PaperScheduleStage f.natDegree M g0,
        s.g = paperBandG M g0 b ∧ s.L = primeBatchLogMean P ∧
          s.U = paperBandScale (Real.exp (paperBandHi f.natDegree m b)) (paperBandG M g0 b)
            (paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + j) := by
    have hjfit : paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + j <
        paperBandOperationCount f.natDegree M m g0 b := by omega
    let o : PaperScheduleOp f.natDegree M g0 :=
      ⟨⟨m, by omega⟩, b, ⟨paperBandEntry (paperBandHi f.natDegree m b) (paperBandG M g0 b) V + j, hjfit⟩⟩
    have ho : o ∈ paperScheduledOps f.natDegree M g0 := by
      simp only [paperScheduledOps, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmlo
    exact ⟨paperOpStage o ho hd hg.1 hg1 T (primeBatchLogMean P)
      (by exact_mod_cast (by omega : 1 < T)) hlogT hmean, rfl, rfl, rfl⟩
  obtain ⟨s0, hsg, hsL, hsU⟩ := hstage 0 (Nat.zero_le l)
  have h0 := hsize M hM s0
  refine ⟨by simpa [hsg] using h0.1, by simpa [hsg] using h0.2.1, ?_, ?_⟩
  · intro j hj
    obtain ⟨s, hsg, hsL, hsU⟩ := hstage j hj.le
    simpa only [hsg, hsL, hsU] using (hsize M hM s).2.2
  · intro j _
    have hb := paperBandEntry_scale_bounds (paperBandHi f.natDegree m b)
      (paperBandG M g0 b) V hg.1 hg1 hV hVhi
    rw [paperBandScale_add]
    exact paperPrimeInventory_geometric_scales P T c _ _ hT hPk hlo hhi hcap
      (paperBandScale_pos _ _ (Real.exp_pos _) hg.1 _).le (hb.2.trans hscale) hg.1.le hg1.le j

/-- Apply the derived block inputs to the ACTUAL finite pair-plus-coin law.
Every transition and recording rank uses its exact scheduled ordinal. -/
theorem paperInventoryBlock_actual_enrichment
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (D M m : ℕ) (g0 : ℝ) (band : Fin 3) (V : ℝ) (l T : ℕ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hinputs : PaperInventoryBlockInputs f D M m g0 band V l P)
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (a : A → ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    let g := paperBandG M g0 band
    let U := fun j => paperBandScale (Real.exp (paperBandHi f.natDegree m band)) g
      (paperBandEntry (paperBandHi f.natDegree m band) g V + j)
    1 - 80 * g - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z (fun j => paperWalkWindow (U j) g) μ a l)
        (paperInputRank (U l) (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (fun j => paperWalkWindow (U j) g) a l ω)) /
        ((paperInputRank (U l) (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  dsimp only
  let g := paperBandG M g0 band
  let U := fun j => paperBandScale (Real.exp (paperBandHi f.natDegree m band)) g
    (paperBandEntry (paperBandHi f.natDegree m band) g V + j)
  have hmatch (j : ℕ) : paperInputRank (U (j + 1)) (primeBatchLogMean P) =
      paperOutputRank (U j) (primeBatchLogMean P) g := by
    dsimp [U, g]
    simpa only [Nat.add_assoc] using paperBandScale_rank_match
      (Real.exp (paperBandHi f.natDegree m band)) (primeBatchLogMean P)
      (paperBandG M g0 band) (paperBandEntry (paperBandHi f.natDegree m band) (paperBandG M g0 band) V + j)
  have h := paper_pairedWalkLaw_enrichment_iterate f hf hd z (fun j => paperWalkWindow (U j) g)
    μ a P hP S hcard hroot e T D l U (fun _ => g)
    (fun j => paperInputRank (U j) (primeBatchLogMean P)) (40 * g)
    hT hPk hlo hhi
    (fun j _ => paperBandScale_pos _ _ (Real.exp_pos _) hinputs.g_pos _)
    (fun _ _ => ⟨hinputs.g_pos, hinputs.g_small⟩) hinputs.size hinputs.inventory
    (fun _ _ => rfl) (fun j _ => ⟨rfl, hmatch j⟩)
    (mul_nonneg (by norm_num) hinputs.g_pos.le) (fun _ _ => le_rfl) hstep hinj
  convert h using 1; ring


/-- Supply the ACTUAL top start, fixed-length block and scalar inputs for every
batch in every window. c,a0 precede l0, every finite exclusion and every walk. -/
theorem paperSchedule_top_inventory_blocks (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (D : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l0 : ℕ, ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∀ M ≥ M0,
        ∀ m : ℕ, (M + 1) / 2 ≤ m → m ≤ M →
          ∀ T : ℕ, 2 ≤ T → paperScheduleX f.natDegree m ≤ Real.log T →
            Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m →
            ∃ P : Finset ℕ, Disjoint P bad ∧
              (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
              0 < P.card ∧ (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
              PaperInventoryBlockInputs f D M m g0 0 (a0 * T) l0 P := by
  obtain ⟨c, hc, hsupply⟩ := exists_paper_prime_inventory f hf hd
  let a0 := min (c / 2) 1
  have ha0 : 0 < a0 := lt_min (by positivity) (by norm_num)
  have ha01 : a0 ≤ 1 := min_le_right _ _
  have ha0c : a0 ≤ c / 2 := min_le_left _ _
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l0 bad
  obtain ⟨T0, hT0⟩ := (hsupply bad).exists_forall_of_atTop
  obtain ⟨Mbatch, hbatch⟩ := paperSchedule_uniform_batch_threshold f.natDegree (by omega) T0
  obtain ⟨Mroom, hroom⟩ := paperSchedule_top_block_fits f.natDegree (by omega) a0 g0
    ha0 ha01 hg0 (by linarith) l0
  obtain ⟨Msize, hsize⟩ := paperSchedule_inventory_block_threshold f D (by omega) g0 hg0 hg064
  refine ⟨max Msize (max Mroom Mbatch), ?_⟩
  intro M hM m hmlo hmhi T hT hlo hhi
  have hMs : Msize ≤ M := (le_max_left _ _).trans hM
  have hMr : Mroom ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMb : Mbatch ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  obtain ⟨P, _, hbad, hP, hPk, hcap, _, hAlpha, _⟩ := hT0 T (hbatch M hMb m hmlo T hlo)
  have hTP : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hVhi : Real.log (a0 * T) ≤ paperBandHi f.natDegree m 0 := by
    rw [Real.log_mul ha0.ne' hTP.ne']
    have ha : Real.log a0 ≤ 0 := Real.log_nonpos ha0.le ha01
    have hx := (paperScheduleX_pos f.natDegree m (by omega)).le
    simp only [paperBandHi, ↓reduceIte]
    linarith
  refine ⟨P, hbad, hP, hPk, hAlpha, ?_⟩
  apply hsize M hMs m hmlo hmhi 0 (a0 * T) c l0 T P (mul_pos ha0 hTP) hVhi
  · simpa only [paperBandG, ↓reduceIte] using hroom M hMr m hmlo T hT hlo hhi
  · exact mul_le_mul_of_nonneg_right ha0c (Nat.cast_nonneg _)
  · exact hT
  · exact hPk
  · exact fun p hp => (hP p hp).2.1
  · exact fun p hp => (hP p hp).2.2.1
  · exact hcap
  · exact hhi


/-- The fixed top block records a rank with positive linear-in-T mass.
One threshold works for every admissible dyadic batch and selected window. -/
theorem paperSchedule_top_record_mass (d : ℕ) (hd : 1 ≤ d) (a0 g0 : ℝ)
    (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (hg0 : 0 < g0) (hg01 : g0 < 1) (l0 : ℕ) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ∀ T : ℕ, 2 ≤ T → paperScheduleX d m ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX d m →
        ∀ P : Finset ℕ, 0 < P.card → (∀ p ∈ P, T ≤ p) → (∀ p ∈ P, p ≤ 2 * T) →
          (((g0 ^ 2) ^ (l0 + 1) * a0) / 2) * T ≤
            (paperInputRank (paperBandScale (Real.exp (paperBandHi d m 0)) g0
              (paperBandEntry (paperBandHi d m 0) g0 (a0 * T) + l0))
              (primeBatchLogMean P) : ℝ) * primeBatchLogMean P := by
  let c0 := ((g0 ^ 2) ^ (l0 + 1) * a0) / 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hlarge : ∀ᶠ T : ℕ in atTop, 2 ≤ c0 * ((T : ℝ) / Real.log T) :=
    ((tendsto_primeCountingScale.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc0).eventually_ge_atTop 2
  obtain ⟨T0, hT0⟩ := hlarge.exists_forall_of_atTop
  obtain ⟨M0, hM0⟩ := paperSchedule_uniform_batch_threshold d hd T0
  refine ⟨M0, ?_⟩
  intro M hM m hm T hT hlo hhi P hPk hPl hPh
  have hl := hT0 T (hM0 M hM m hm T hlo)
  have hTP : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hPl hPh
  have hlog2 : Real.log 2 ≤ Real.log (T : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have htw : Real.log (2 * T : ℕ) ≤ 2 * Real.log (T : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hTP.ne']
    linarith
  have hbudget : primeBatchLogMean P ≤ c0 * T := by
    have hb : 2 * Real.log (T : ℝ) ≤ c0 * T := by
      apply (le_div_iff₀ hlog).mp
      simpa only [mul_div_assoc] using hl
    exact hL.2.2.1.trans (htw.trans hb)
  have hVhi : Real.log (a0 * T) ≤ paperBandHi d m 0 := by
    rw [Real.log_mul ha0.ne' hTP.ne']
    have ha : Real.log a0 ≤ 0 := Real.log_nonpos ha0.le ha01
    have hx := (paperScheduleX_pos d m hd).le
    simp only [paperBandHi, ↓reduceIte]
    linarith
  have hsmall : primeBatchLogMean P ≤ ((g0 ^ 2) ^ (l0 + 1) * (a0 * T)) / 2 := by
    convert hbudget using 1; dsimp [c0]; ring
  have h := paperBandEntry_record_rank_mass (paperBandHi d m 0) g0 (a0 * T)
    (primeBatchLogMean P) hg0 hg01 (mul_pos ha0 hTP) hVhi hL.1 l0 hsmall
  convert h using 1; ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.PaperInventoryBlockInputs
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_inventory_block_threshold
#print axioms BinaryFormMoat.GeometryIntegration.paperInventoryBlock_actual_enrichment

#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_top_inventory_blocks

#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_top_record_mass
