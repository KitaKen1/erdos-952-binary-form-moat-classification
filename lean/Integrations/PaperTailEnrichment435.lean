import Integrations.PairedWalkTail435
import Integrations.PaperGlobalBlock435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Enrichment inside a fresh remaining-schedule experiment, retaining its
exact law and all pre-block history. All starting laws are allowed. -/
theorem paper_pairedWalkTailLaw_enrichment_interval
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T D r0 m : ℕ) (U g : ℕ → ℝ) (rank : ℕ → ℕ) (δ : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hU : ∀ n < m, 0 < U n) (hg : ∀ n < m, 0 < g n ∧ g n < 1 / 64)
    (hsize : ∀ n < m, paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g n ^ 10 * U n)
    (hinventory : ∀ n < m, paperInputRank (U n) (primeBatchLogMean P) ≤ P.card)
    (hN : ∀ n < m, N (k + (r0 + n)) = paperWalkWindow (U n) (g n))
    (hmatch : ∀ n < m, rank n = paperInputRank (U n) (primeBatchLogMean P) ∧
      rank (n + 1) = paperOutputRank (U n) (primeBatchLogMean P) (g n))
    (hδ : 0 ≤ δ) (herror : ∀ n < m, 40 * g n ≤ δ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z N b k ν (r0 + m)) (rank m) (fun a => z (pairedWalkTime N b (k + (r0 + m)) a)) /
        ((rank m : ℝ) * primeBatchLogMean P) := by
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  let h := fun n => labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
    (pairedWalkTailLaw z N b k ν (r0 + n)) (rank n) (fun a => z (pairedWalkTime N b (k + (r0 + n)) a)) /
    ((rank n : ℝ) * primeBatchLogMean P)
  apply normalized_enrichment_iterate_prefix_nonneg h δ m hδ
  · exact div_nonneg (labelledPointEntropyMean_nonneg _ _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) hL.le)
  · intro n hn
    have hi := paper_prime_subset_paired_enrichment f hf hd z (U n) (g n)
      (pairedWalkTailLaw z N b k ν (r0 + n)) (pairedWalkTime N b (k + (r0 + n))) P hP S hcard hroot e T D
      (hU n hn) (hg n hn).1 (hg n hn).2 hT hPk hlo hhi (hsize n hn) (hinventory n hn)
      hstep (fun _ _ _ _ _ _ he => Nat.add_left_cancel (hinj he))
    rw [← hN n hn, pairedWalkPoint_step_eq, ← (hmatch n hn).1, ← (hmatch n hn).2] at hi
    change (1 + h n) / 2 - 40 * g n ≤ h (n + 1) at hi
    linarith [herror n hn]



/-- An actual contiguous inventory block enriches every experiment begun at
any earlier checkpoint, including arbitrary exact starts and positive fibers. -/
theorem paperInventoryBlock_tail_enrichment
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
    (z : ℕ → Point) (a : A → ℕ) (k0 : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k0))
    [IsProbabilityMeasure ν]
    (hbefore : k0 ≤ paperOpPosition (d := f.natDegree) (g0 := g0)
      ⟨m, band, ⟨paperBandEntry (paperBandHi f.natDegree m.val band)
        (paperBandG M g0 band) V, by omega⟩⟩)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    let g := paperBandG M g0 band
    let n := paperBandEntry (paperBandHi f.natDegree m.val band) g V
    let k := paperOpPosition (d := f.natDegree) (g0 := g0) ⟨m, band, ⟨n, by dsimp [n, g]; omega⟩⟩
    let U := fun j => paperBandScale (Real.exp (paperBandHi f.natDegree m.val band)) g (n + j)
    1 - 80 * g - (1 / 2 : ℝ) ^ l ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k0 ν (k - k0 + l))
        (paperInputRank (U l) (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k0 + (k - k0 + l)) ω)) /
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
  have hk : k0 + (k - k0) = k := by dsimp [k, n, g]; omega
  have hNtail (j : ℕ) (hj : j < l) :
      paperScheduleWindow f.natDegree M g0 (k0 + (k - k0 + j)) = paperWalkWindow (U j) g := by
    simpa only [← Nat.add_assoc, hk] using hN j hj
  have h := paper_pairedWalkTailLaw_enrichment_interval f hf hd z (paperScheduleWindow f.natDegree M g0)
    a k0 ν P hP S hcard hroot e T D (k - k0) l U (fun _ => g)
    (fun j => paperInputRank (U j) (primeBatchLogMean P)) (40 * g)
    hT hPk hlo hhi
    (fun j _ => paperBandScale_pos _ _ (Real.exp_pos _) hinputs.g_pos _)
    (fun _ _ => ⟨hinputs.g_pos, hinputs.g_small⟩) hinputs.size hinputs.inventory hNtail
    (fun j _ => ⟨rfl, hmatch j⟩)
    (mul_nonneg (by norm_num) hinputs.g_pos.le) (fun _ _ => le_rfl) hstep hinj
  convert h using 1; ring

/-- The iterated lower bound on every positive EARLIER checkpoint fiber.
No conditioning on the recording time or terminal residue is used. -/
theorem paper_pairedWalkTailLaw_cond_enrichment_interval
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N k → B) (c : B) (hc : ν (V ⁻¹' {c}) ≠ 0)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T D r0 m : ℕ) (U g : ℕ → ℝ) (rank : ℕ → ℕ) (δ : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hU : ∀ n < m, 0 < U n) (hg : ∀ n < m, 0 < g n ∧ g n < 1 / 64)
    (hsize : ∀ n < m, paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g n ^ 10 * U n)
    (hinventory : ∀ n < m, paperInputRank (U n) (primeBatchLogMean P) ≤ P.card)
    (hN : ∀ n < m, N (k + (r0 + n)) = paperWalkWindow (U n) (g n))
    (hmatch : ∀ n < m, rank n = paperInputRank (U n) (primeBatchLogMean P) ∧
      rank (n + 1) = paperOutputRank (U n) (primeBatchLogMean P) (g n))
    (hδ : 0 ≤ δ) (herror : ∀ n < m, 40 * g n ≤ δ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        ((pairedWalkTailLaw z N b k ν (r0 + m))[|
          (fun ω => V (pairedWalkPast N k (r0 + m) ω)) ⁻¹' {c}]) (rank m) (fun a => z (pairedWalkTime N b (k + (r0 + m)) a)) /
        ((rank m : ℝ) * primeBatchLogMean P) := by
  let := cond_isProbabilityMeasure (μ := ν) hc
  rw [pairedWalkTailLaw_cond_checkpoint z N b k ν (r0 + m) V c]
  exact paper_pairedWalkTailLaw_enrichment_interval f hf hd z N b k (ν[|V ⁻¹' {c}])
    P hP S hcard hroot e T D r0 m U g rank δ hT hPk hlo hhi hU hg hsize hinventory
    hN hmatch hδ herror hstep hinj

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paper_pairedWalkTailLaw_enrichment_interval

#print axioms BinaryFormMoat.GeometryIntegration.paperInventoryBlock_tail_enrichment

#print axioms BinaryFormMoat.GeometryIntegration.paper_pairedWalkTailLaw_cond_enrichment_interval
