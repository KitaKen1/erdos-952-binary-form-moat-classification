import Integrations.PaperInventoryBlock435
import Integrations.PaperScheduleBlocks435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Restart the scalar recurrence inside the ORIGINAL full process. No new
probability law, history equivalence or transition independence is assumed. -/
theorem paper_pairedWalkLaw_enrichment_interval
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T D k m : ℕ) (U g : ℕ → ℝ) (rank : ℕ → ℕ) (δ : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hU : ∀ n < m, 0 < U n) (hg : ∀ n < m, 0 < g n ∧ g n < 1 / 64)
    (hsize : ∀ n < m, paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g n ^ 10 * U n)
    (hinventory : ∀ n < m, paperInputRank (U n) (primeBatchLogMean P) ≤ P.card)
    (hN : ∀ n < m, N (k + n) = paperWalkWindow (U n) (g n))
    (hmatch : ∀ n < m, rank n = paperInputRank (U n) (primeBatchLogMean P) ∧
      rank (n + 1) = paperOutputRank (U n) (primeBatchLogMean P) (g n))
    (hδ : 0 ≤ δ) (herror : ∀ n < m, 40 * g n ≤ δ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z N μ b (k + m)) (rank m) (fun a => z (pairedWalkTime N b (k + m) a)) /
        ((rank m : ℝ) * primeBatchLogMean P) := by
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  let h := fun n => labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
    (pairedWalkLaw z N μ b (k + n)) (rank n) (fun a => z (pairedWalkTime N b (k + n) a)) /
    ((rank n : ℝ) * primeBatchLogMean P)
  apply normalized_enrichment_iterate_prefix_nonneg h δ m hδ
  · exact div_nonneg (labelledPointEntropyMean_nonneg _ _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) hL.le)
  · intro n hn
    have hi := paper_prime_subset_paired_enrichment f hf hd z (U n) (g n)
      (pairedWalkLaw z N μ b (k + n)) (pairedWalkTime N b (k + n)) P hP S hcard hroot e T D
      (hU n hn) (hg n hn).1 (hg n hn).2 hT hPk hlo hhi (hsize n hn) (hinventory n hn)
      hstep (fun _ _ _ _ _ _ he => Nat.add_left_cancel (hinj he))
    rw [← hN n hn, pairedWalkPoint_step_eq, ← (hmatch n hn).1, ← (hmatch n hn).2] at hi
    change (1 + h n) / 2 - 40 * g n ≤ h (n + 1) at hi
    linarith [herror n hn]


/-- The inventory block's deficit holds at its actual recording index in ONE
common schedule. All pre-block history and its exact law are retained. -/
theorem paperInventoryBlock_global_enrichment
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (D M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 : ℝ) (band : Fin 3) (V : ℝ) (l T : ℕ)
    (hfit : paperBandEntry (paperBandHi f.natDegree m.val band) (paperBandG M g0 band) V + l <
      paperBandOperationCount f.natDegree M m.val g0 band)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hinputs : PaperInventoryBlockInputs f D M m.val g0 band V l P)
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (a : A → ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    let g := paperBandG M g0 band
    let n := paperBandEntry (paperBandHi f.natDegree m.val band) g V
    let k := paperOpPosition (d := f.natDegree) (g0 := g0) ⟨m, band, ⟨n, by dsimp [n, g]; omega⟩⟩
    let U := fun j => paperBandScale (Real.exp (paperBandHi f.natDegree m.val band)) g (n + j)
    1 - 80 * g - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z (paperScheduleWindow f.natDegree M g0) μ a (k + l))
        (paperInputRank (U l) (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k + l) ω)) /
        ((paperInputRank (U l) (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  dsimp only
  let g := paperBandG M g0 band
  let n := paperBandEntry (paperBandHi f.natDegree m.val band) g V
  have hn : n < paperBandOperationCount f.natDegree M m.val g0 band := by dsimp [n, g]; omega
  let k := paperOpPosition (d := f.natDegree) (g0 := g0) ⟨m, band, ⟨n, hn⟩⟩
  let U := fun j => paperBandScale (Real.exp (paperBandHi f.natDegree m.val band)) g (n + j)
  have hmatch (j : ℕ) : paperInputRank (U (j + 1)) (primeBatchLogMean P) =
      paperOutputRank (U j) (primeBatchLogMean P) g := by
    dsimp [U, g]
    simpa only [Nat.add_assoc] using paperBandScale_rank_match
      (Real.exp (paperBandHi f.natDegree m.val band)) (primeBatchLogMean P)
      (paperBandG M g0 band) (n + j)
  have hN (j : ℕ) (hj : j < l) :
      paperScheduleWindow f.natDegree M g0 (k + j) = paperWalkWindow (U j) g := by
    exact paperScheduleWindow_block m hm band n j (by dsimp [n, g]; omega)
  have h := paper_pairedWalkLaw_enrichment_interval f hf hd z (paperScheduleWindow f.natDegree M g0)
    μ a P hP S hcard hroot e T D k l U (fun _ => g)
    (fun j => paperInputRank (U j) (primeBatchLogMean P)) (40 * g)
    hT hPk hlo hhi
    (fun j _ => paperBandScale_pos _ _ (Real.exp_pos _) hinputs.g_pos _)
    (fun _ _ => ⟨hinputs.g_pos, hinputs.g_small⟩) hinputs.size hinputs.inventory hN
    (fun j _ => ⟨rfl, hmatch j⟩)
    (mul_nonneg (by norm_num) hinputs.g_pos.le) (fun _ _ => le_rfl) hstep hinj
  convert h using 1; ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paper_pairedWalkLaw_enrichment_interval
#print axioms BinaryFormMoat.GeometryIntegration.paperInventoryBlock_global_enrichment
