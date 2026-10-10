import Integrations.PaperEnrichmentQuota435
import Integrations.PairedWalkIteration435
import Mathlib.Order.Filter.Finite

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory Filter

section Paired
variable {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype R] [Nonempty R]
  (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
  (z : ℕ → Point) (U g : ℝ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
  (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
  (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
  (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
  (e : ∀ p : P, R ≃ S p.val) (T D : ℕ)
  (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64) (hT : 2 ≤ T) (hPk : 0 < P.card)
  (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
  (hsize : paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g ^ 10 * U)
  (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
  (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
  (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ paperWalkWindow U g, ∀ j ≤ paperWalkWindow U g,
    z (b a + i) = z (b a + j) → i = j)

include hf hd hP hcard hroot hU hg hg64 hT hPk hlo hhi hsize hinventory hstep hinj

/-- Quantitative paper Lemma 4.3 on the ACTUAL law: all primitive quotas are
derived, with the paper's floors and a fixed error 40g. -/
theorem paper_prime_subset_paired_enrichment :
    (1 + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      μ (paperInputRank U (primeBatchLogMean P)) (fun a => z (b a)) /
      ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)) / 2 - 40 * g ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (fairEndpointLaw (differencePairForwardLaw z (paperWalkWindow U g) μ b))
      (paperOutputRank U (primeBatchLogMean P) g)
      (fairEndpointPoint (fun ω => z (differencePairFirstTime (paperWalkWindow U g) b ω))
        (fun ω => z (differencePairSecondTime (paperWalkWindow U g) b ω))) /
      ((paperOutputRank U (primeBatchLogMean P) g : ℝ) * primeBatchLogMean P) := by
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hL2 : Real.log 2 ≤ primeBatchLogMean P :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans hL.2.1
  have hs := paperEnrichment_size_inputs f D U (primeBatchLogMean P) g hU hL.1 hL2
    hg (by linarith) hsize
  have hr := paperRank_pair_bounds U (primeBatchLogMean P) g hU hL.1 hg hg64 hs.2.1
  have h := constructed_prime_subset_paired_enrichment f hf hd z (paperWalkWindow U g) μ b
    P hP S hcard hroot e (paperOutputRank U (primeBatchLogMean P) g)
    (paperInputRank U (primeBatchLogMean P)) D T hr.1 hr.2.1 hinventory hT (8 * g)
    (by positivity) (by linarith) hlo hhi (g * U + Real.log 2)
    (paperWalkWindow_log_bounds U g (by positivity)).2 hstep hinj
    (fun a _ => paper_walk_enrichment_quota f (fun k => z (b a + k)) D U g P T
      hU hT hPk hlo hhi hg hg64 hsize hinventory
      (fun t _ => by simpa only [← Nat.add_assoc] using hstep (b a + t)))
    (paper_enrichment_physical_quota f D U g P T hU hT hPk hlo hhi hg hg64 hsize)
  convert h using 1; ring

theorem paper_prime_subset_cond_paired_enrichment
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : A → B) (c : B) (hc : μ (V ⁻¹' {c}) ≠ 0) :
    (1 + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (μ[|V ⁻¹' {c}]) (paperInputRank U (primeBatchLogMean P)) (fun a => z (b a)) /
      ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)) / 2 - 40 * g ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      ((fairEndpointLaw (differencePairForwardLaw z (paperWalkWindow U g) μ b))[|(fun ω => V ω.1.1) ⁻¹' {c}])
      (paperOutputRank U (primeBatchLogMean P) g)
      (fairEndpointPoint (fun ω => z (differencePairFirstTime (paperWalkWindow U g) b ω))
        (fun ω => z (differencePairSecondTime (paperWalkWindow U g) b ω))) /
      ((paperOutputRank U (primeBatchLogMean P) g : ℝ) * primeBatchLogMean P) := by
  let := cond_isProbabilityMeasure (μ := μ) (s := V ⁻¹' {c}) hc
  rw [differencePairFairLaw_cond_checkpoint z (paperWalkWindow U g) μ b V c]
  apply paper_prime_subset_paired_enrichment f hf hd z U g (μ[|V ⁻¹' {c}]) b
    P hP S hcard hroot e T D hU hg hg64 hT hPk hlo hhi hsize hinventory hstep
  intro a ha
  exact hinj a (cond_singleton_ne_zero_imp μ _ a ha)

end Paired

/-- Only C=10 of the manuscript's all-fixed-power regime is needed for the
derived local enrichment criterion. L is the TRUE mean, bounded above by 2log T. -/
theorem paperEnrichmentSize_eventually {α : Type*} (l : Filter α)
    (f : Polynomial ℤ) (D : ℕ) (U g L T : α → ℝ)
    (hT : ∀ᶠ x in l, 1 < T x) (hL : ∀ᶠ x in l, L x ≤ 2 * Real.log (T x))
    (hregime : Tendsto (fun x => g x ^ 10 * U x / Real.log (T x)) l atTop) :
    ∀ᶠ x in l, paperEnrichmentSizeConstant f D * L x ≤ g x ^ 10 * U x := by
  have hC := paperEnrichmentSizeConstant_pos f D
  filter_upwards [hT, hL, hregime.eventually_ge_atTop (2 * paperEnrichmentSizeConstant f D)]
    with x hx hl hr
  have hlog : 0 < Real.log (T x) := Real.log_pos hx
  have hb := (le_div_iff₀ hlog).mp hr
  have hm := mul_le_mul_of_nonneg_left hl hC.le
  nlinarith

/-- A fixed finite family has a common numeric threshold. This does not assert
uniformity for a family whose number of stages grows with x. -/
theorem paperEnrichmentSize_eventually_finite {α ι : Type*} [Finite ι] (l : Filter α)
    (f : Polynomial ℤ) (D : ℕ) (U g L T : ι → α → ℝ)
    (hT : ∀ i, ∀ᶠ x in l, 1 < T i x)
    (hL : ∀ i, ∀ᶠ x in l, L i x ≤ 2 * Real.log (T i x))
    (hregime : ∀ i, Tendsto (fun x => g i x ^ 10 * U i x / Real.log (T i x)) l atTop) :
    ∀ᶠ x in l, ∀ i, paperEnrichmentSizeConstant f D * L i x ≤ g i x ^ 10 * U i x := by
  exact Filter.eventually_all.mpr (fun i => paperEnrichmentSize_eventually l f D
    (U i) (g i) (L i) (T i) (hT i) (hL i) (hregime i))

theorem paperEnrichmentSize_exists_common_threshold {ι : Type*} [Finite ι]
    (f : Polynomial ℤ) (D : ℕ) (U g L T : ι → ℕ → ℝ)
    (hT : ∀ i, ∀ᶠ m in atTop, 1 < T i m)
    (hL : ∀ i, ∀ᶠ m in atTop, L i m ≤ 2 * Real.log (T i m))
    (hregime : ∀ i, Tendsto (fun m => g i m ^ 10 * U i m / Real.log (T i m)) atTop atTop) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i, paperEnrichmentSizeConstant f D * L i m ≤ g i m ^ 10 * U i m := by
  exact (paperEnrichmentSize_eventually_finite atTop f D U g L T hT hL hregime).exists_forall_of_atTop

/-- Extremal parameter bounds give one threshold even when the index type and
number of operations grow with x. No finite-family limit interchange is used. -/
theorem paperEnrichmentSize_eventually_uniform {α : Type*} (l : Filter α)
    (ι : α → Type*) (f : Polynomial ℤ) (D : ℕ) (Umin gmin Tmax : α → ℝ)
    (U g L : (x : α) → ι x → ℝ)
    (hT : ∀ᶠ x in l, 1 < Tmax x)
    (hpos : ∀ᶠ x in l, 0 ≤ Umin x ∧ 0 ≤ gmin x)
    (hbound : ∀ᶠ x in l, ∀ i, gmin x ≤ g x i ∧ Umin x ≤ U x i ∧
      L x i ≤ 2 * Real.log (Tmax x))
    (hregime : Tendsto (fun x => gmin x ^ 10 * Umin x / Real.log (Tmax x)) l atTop) :
    ∀ᶠ x in l, ∀ i, paperEnrichmentSizeConstant f D * L x i ≤ g x i ^ 10 * U x i := by
  have hb := paperEnrichmentSize_eventually l f D Umin gmin
    (fun x => 2 * Real.log (Tmax x)) Tmax hT (Eventually.of_forall (fun _ => le_rfl)) hregime
  have hC := (paperEnrichmentSizeConstant_pos f D).le
  filter_upwards [hb, hpos, hbound] with x hx hp hs
  intro i
  have hg : 0 ≤ g x i := hp.2.trans (hs i).1
  have hpow : gmin x ^ 10 ≤ g x i ^ 10 := by
    gcongr
    · exact hp.2
    · exact (hs i).1
  have hm := mul_le_mul hpow (hs i).2.1 hp.1 (pow_nonneg hg 10)
  exact (mul_le_mul_of_nonneg_left (hs i).2.2 hC).trans (hx.trans hm)

/-- Apply the derived paper criterion to each step of the actual finite process.
No geometric floor, failure probability or recurrence is assumed. -/
theorem paper_pairedWalkLaw_enrichment_iterate
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (N : ℕ → ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T D m : ℕ) (U g : ℕ → ℝ) (rank : ℕ → ℕ) (δ : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hU : ∀ n < m, 0 < U n) (hg : ∀ n < m, 0 < g n ∧ g n < 1 / 64)
    (hsize : ∀ n < m, paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g n ^ 10 * U n)
    (hinventory : ∀ n < m, paperInputRank (U n) (primeBatchLogMean P) ≤ P.card)
    (hN : ∀ n < m, N n = paperWalkWindow (U n) (g n))
    (hmatch : ∀ n < m, rank n = paperInputRank (U n) (primeBatchLogMean P) ∧
      rank (n + 1) = paperOutputRank (U n) (primeBatchLogMean P) (g n))
    (hδ : 0 ≤ δ) (herror : ∀ n < m, 40 * g n ≤ δ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    1 - 2 * δ - (1 / 2 : ℝ) ^ m ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z N μ b m) (rank m) (fun a => z (pairedWalkTime N b m a)) /
        ((rank m : ℝ) * primeBatchLogMean P) := by
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  let h := fun n => labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
    (pairedWalkLaw z N μ b n) (rank n) (fun a => z (pairedWalkTime N b n a)) /
    ((rank n : ℝ) * primeBatchLogMean P)
  apply normalized_enrichment_iterate_prefix_nonneg h δ m hδ
  · exact div_nonneg (labelledPointEntropyMean_nonneg _ _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) hL.le)
  · intro n hn
    have hi := paper_prime_subset_paired_enrichment f hf hd z (U n) (g n)
      (pairedWalkLaw z N μ b n) (pairedWalkTime N b n) P hP S hcard hroot e T D
      (hU n hn) (hg n hn).1 (hg n hn).2 hT hPk hlo hhi (hsize n hn) (hinventory n hn)
      hstep (fun _ _ _ _ _ _ he => Nat.add_left_cancel (hinj he))
    rw [← hN n hn, pairedWalkPoint_step_eq, ← (hmatch n hn).1, ← (hmatch n hn).2] at hi
    change (1 + h n) / 2 - 40 * g n ≤ h (n + 1) at hi
    linarith [herror n hn]

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paper_prime_subset_paired_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.paper_prime_subset_cond_paired_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSize_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSize_eventually_finite
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSize_exists_common_threshold
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSize_eventually_uniform
#print axioms BinaryFormMoat.GeometryIntegration.paper_pairedWalkLaw_enrichment_iterate
