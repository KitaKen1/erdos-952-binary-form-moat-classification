import Integrations.PaperScheduleExtremes435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The exact geometric progression of scales within one paper band. -/
def paperBandScale (U g : ℝ) (n : ℕ) : ℝ := (g ^ 2) ^ n * U

theorem paperBandScale_pos (U g : ℝ) (hU : 0 < U) (hg : 0 < g) (n : ℕ) :
    0 < paperBandScale U g n := by unfold paperBandScale; positivity

theorem paperBandScale_succ (U g : ℝ) (n : ℕ) :
    paperBandScale U g (n + 1) = g ^ 2 * paperBandScale U g n := by
  unfold paperBandScale
  rw [pow_succ]
  ring

theorem paperBandScale_antitone (U g : ℝ) (hU : 0 ≤ U) (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    Antitone (paperBandScale U g) := by
  intro i j hij
  have hsq : g ^ 2 ≤ 1 := by nlinarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (sq_nonneg g) hsq hij) hU

theorem paperBandScale_log (U g : ℝ) (hU : 0 < U) (hg : 0 < g) (n : ℕ) :
    Real.log (paperBandScale U g n) = Real.log U + 2 * n * Real.log g := by
  unfold paperBandScale
  rw [Real.log_mul (by positivity) hU.ne', Real.log_pow, Real.log_pow]
  norm_num
  ring

def paperBandLogStep (g : ℝ) : ℝ := 2 * Real.log (1 / g)
def paperBandLength (lo hi g : ℝ) : ℕ := ⌊(hi - lo) / paperBandLogStep g⌋₊ + 1

theorem paperBandLogStep_pos (g : ℝ) (hg : 0 < g) (hg1 : g < 1) :
    0 < paperBandLogStep g := by
  unfold paperBandLogStep
  apply mul_pos (by norm_num)
  apply Real.log_pos
  exact (lt_div_iff₀ hg).mpr (by simpa using hg1)

/-- Every listed scale lies inside the closed band. This constructs the finite
within-band operation count rather than assuming matched scales. -/
theorem paperBandScale_mem_band (lo hi g : ℝ) (hband : lo ≤ hi)
    (hg : 0 < g) (hg1 : g < 1) (n : ℕ) (hn : n < paperBandLength lo hi g) :
    lo ≤ Real.log (paperBandScale (Real.exp hi) g n) ∧
      Real.log (paperBandScale (Real.exp hi) g n) ≤ hi := by
  have hs := paperBandLogStep_pos g hg hg1
  have hf : n ≤ ⌊(hi - lo) / paperBandLogStep g⌋₊ := by
    unfold paperBandLength at hn
    omega
  have hcast : (n : ℝ) ≤ (⌊(hi - lo) / paperBandLogStep g⌋₊ : ℝ) := by
    exact_mod_cast hf
  have hc : (n : ℝ) ≤ (hi - lo) / paperBandLogStep g :=
    hcast.trans (Nat.floor_le (div_nonneg (by linarith) hs.le))
  have hm := (le_div_iff₀ hs).mp hc
  have he : paperBandLogStep g = -2 * Real.log g := by
    unfold paperBandLogStep
    rw [Real.log_div (by norm_num) hg.ne', Real.log_one]
    ring
  have hp : 0 ≤ (n : ℝ) * paperBandLogStep g := by positivity
  rw [paperBandScale_log _ _ (Real.exp_pos hi) hg, Real.log_exp]
  rw [he] at hm hp
  constructor <;> nlinarith

theorem paperBandScale_rank_match (U L g : ℝ) (n : ℕ) :
    paperInputRank (paperBandScale U g (n + 1)) L =
      paperOutputRank (paperBandScale U g n) L g := by
  rw [paperBandScale_succ]
  rfl

/-- Concrete geometric scales, exact paper windows and exact floor ranks feed
the actual finite process. A LAST-step size criterion and FIRST-step inventory
are sufficient for every step. The entropy recurrence is derived. -/
theorem paperBand_actual_enrichment_iterate
    {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T D m : ℕ) (U g : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64) (hm : 0 < m)
    (hsize : paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤
      g ^ 10 * paperBandScale U g (m - 1))
    (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : Function.Injective z) :
    1 - 80 * g - (1 / 2 : ℝ) ^ m ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z (fun n => paperWalkWindow (paperBandScale U g n) g) μ b m)
        (paperInputRank (paperBandScale U g m) (primeBatchLogMean P))
        (fun a => z (pairedWalkTime (fun n => paperWalkWindow (paperBandScale U g n) g) b m a)) /
        ((paperInputRank (paperBandScale U g m) (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hant := paperBandScale_antitone U g hU.le hg.le (by linarith)
  have hs (n : ℕ) (hn : n < m) : paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤
      g ^ 10 * paperBandScale U g n :=
    hsize.trans (mul_le_mul_of_nonneg_left (hant (by omega : n ≤ m - 1)) (by positivity))
  have hi (n : ℕ) : paperInputRank (paperBandScale U g n) (primeBatchLogMean P) ≤ P.card := by
    have hu : paperBandScale U g n ≤ U := by simpa [paperBandScale] using hant (Nat.zero_le n)
    exact (Nat.floor_mono (div_le_div_of_nonneg_right hu hL.le)).trans hinventory
  have h := paper_pairedWalkLaw_enrichment_iterate f hf hd z
    (fun n => paperWalkWindow (paperBandScale U g n) g) μ b P hP S hcard hroot e T D m
    (paperBandScale U g) (fun _ => g)
    (fun n => paperInputRank (paperBandScale U g n) (primeBatchLogMean P)) (40 * g)
    hT hPk hlo hhi (fun n _ => paperBandScale_pos U g hU hg n) (fun _ _ => ⟨hg, hg64⟩)
    hs (fun n _ => hi n) (fun _ _ => rfl)
    (fun n _ => ⟨rfl, paperBandScale_rank_match U _ g n⟩) (by positivity) (fun _ _ => le_rfl) hstep hinj
  convert h using 1; ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_antitone
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_log
#print axioms BinaryFormMoat.GeometryIntegration.paperBandLogStep
#print axioms BinaryFormMoat.GeometryIntegration.paperBandLength
#print axioms BinaryFormMoat.GeometryIntegration.paperBandLogStep_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_mem_band
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_rank_match
#print axioms BinaryFormMoat.GeometryIntegration.paperBand_actual_enrichment_iterate
