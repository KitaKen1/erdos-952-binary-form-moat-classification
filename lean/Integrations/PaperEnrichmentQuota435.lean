import Integrations.PaperWalkWindow435
import Integrations.PaperRankBudget435
import Integrations.ConstructedSeparationEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open HarperIntegration EntropyIntegration

def paperWalkPhysicalConstant (D : ℕ) : ℝ :=
  4 * Real.log 2 + 4 * Real.log (4 * D + 1 : ℕ)

/-- One fixed f,D cost covers geometry, separation overhead and physical motion. -/
def paperEnrichmentFixedCost (f : Polynomial ℤ) (D : ℕ) : ℝ :=
  max 1 (max (walkSeparationFixedOverhead f D)
    (max (paperWalkAreaConstant D) (paperWalkPhysicalConstant D)))

/-- A single size threshold absorbs fixed costs and the coarse Harper rate. -/
def paperEnrichmentSizeConstant (f : Polynomial ℤ) (D : ℕ) : ℝ :=
  19 + 2099520 * f.natDegree + paperEnrichmentFixedCost f D / Real.log 2

theorem paperEnrichmentFixedCost_bounds (f : Polynomial ℤ) (D : ℕ) :
    1 ≤ paperEnrichmentFixedCost f D ∧
      walkSeparationFixedOverhead f D ≤ paperEnrichmentFixedCost f D ∧
      paperWalkAreaConstant D ≤ paperEnrichmentFixedCost f D ∧
      paperWalkPhysicalConstant D ≤ paperEnrichmentFixedCost f D ∧
      2 * Real.log (4 * D + 1 : ℕ) ≤ paperEnrichmentFixedCost f D := by
  have h1 : 1 ≤ paperEnrichmentFixedCost f D := le_max_left _ _
  have h := le_max_right (1 : ℝ)
    (max (walkSeparationFixedOverhead f D)
      (max (paperWalkAreaConstant D) (paperWalkPhysicalConstant D)))
  have hH := (le_max_left (walkSeparationFixedOverhead f D) _).trans h
  have ha := (le_max_left (paperWalkAreaConstant D) _).trans
    ((le_max_right (walkSeparationFixedOverhead f D) _).trans h)
  have hp := (le_max_right (paperWalkAreaConstant D) _).trans
    ((le_max_right (walkSeparationFixedOverhead f D) _).trans h)
  have hdlog : 0 ≤ Real.log (4 * D + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 4 * D + 1))
  refine ⟨h1, hH, ha, hp, ?_⟩
  change paperWalkPhysicalConstant D ≤ paperEnrichmentFixedCost f D at hp
  unfold paperWalkPhysicalConstant at hp
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

theorem paperEnrichmentSizeConstant_pos (f : Polynomial ℤ) (D : ℕ) :
    0 < paperEnrichmentSizeConstant f D := by
  have hK := (paperEnrichmentFixedCost_bounds f D).1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold paperEnrichmentSizeConstant
  positivity

/-- The paper's C=10 size criterion supplies every fixed cost and the three
area-scale rounding/tail inputs, with internal slack equal to 8g. -/
theorem paperEnrichment_size_inputs (f : Polynomial ℤ) (D : ℕ) (U L g : ℝ)
    (hU : 0 < U) (hL : 0 < L) (hL2 : Real.log 2 ≤ L)
    (hg : 0 < g) (hg1 : g ≤ 1)
    (hsize : paperEnrichmentSizeConstant f D * L ≤ g ^ 10 * U) :
    paperEnrichmentFixedCost f D ≤ g ^ 2 * U ∧ L ≤ g ^ 2 * U ∧
      (19 + 2099520 * f.natDegree) * L ≤ (8 * g) ^ 9 * (g * U) := by
  let K := paperEnrichmentFixedCost f D
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans (paperEnrichmentFixedCost_bounds f D).1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 ≤ (19 + 2099520 * (f.natDegree : ℝ)) := by positivity
  have hterm : 0 ≤ K / Real.log 2 := div_nonneg hK hlog.le
  have hkL := mul_le_mul_of_nonneg_left hL2 hterm
  have hk : K ≤ g ^ 10 * U := by
    have he : (K / Real.log 2) * Real.log 2 = K := div_mul_cancel₀ K hlog.ne'
    change (19 + 2099520 * (f.natDegree : ℝ) + K / Real.log 2) * L ≤ g ^ 10 * U at hsize
    nlinarith [mul_nonneg hbase hL.le]
  have hLbig : L ≤ g ^ 10 * U := by
    change (19 + 2099520 * (f.natDegree : ℝ) + K / Real.log 2) * L ≤ g ^ 10 * U at hsize
    nlinarith [mul_nonneg hterm hL.le, mul_nonneg (Nat.cast_nonneg f.natDegree) hL.le]
  have hpow : g ^ 10 ≤ g ^ 2 := by
    calc
      _ = g ^ 2 * g ^ 8 := by ring
      _ ≤ g ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hg.le hg1) (sq_nonneg g)
      _ = _ := mul_one _
  have hpowU := mul_le_mul_of_nonneg_right hpow hU.le
  have hr : g ^ 10 * U ≤ (8 * g) ^ 9 * (g * U) := by
    have hp : 0 ≤ g ^ 10 * U := by positivity
    nlinarith [show (8 * g) ^ 9 * (g * U) = 134217728 * (g ^ 10 * U) by ring]
  have hb : (19 + 2099520 * (f.natDegree : ℝ)) * L ≤ g ^ 10 * U := by
    unfold paperEnrichmentSizeConstant at hsize
    nlinarith [mul_nonneg hterm hL.le]
  exact ⟨hk.trans hpowU, hLbig.trans hpowU, hb.trans hr⟩

/-- All primitive geometric/separation/inventory quotas now follow uniformly
for bounded-step walks from ONE scalar paper-scale size condition. -/
theorem paper_walk_enrichment_quota (f : Polynomial ℤ) (z : ℕ → Point) (D : ℕ)
    (U g : ℝ) (P : Finset ℕ) (T : ℕ) (hU : 0 < U)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hg : 0 < g) (hg64 : g < 1 / 64)
    (hsize : paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g ^ 10 * U)
    (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
    (hstep : ∀ t < paperWalkWindow U g,
      |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D) :
    ConstructedWalkEnrichmentQuota f z D (paperWalkWindow U g) P T
      (paperOutputRank U (primeBatchLogMean P) g) (8 * g) := by
  let L := primeBatchLogMean P
  let A := walkSeparationAreaLog z (paperWalkWindow U g)
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hL2 : Real.log 2 ≤ L :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans hL.2.1
  have hs := paperEnrichment_size_inputs f D U L g hU hL.1 hL2 hg (by linarith) hsize
  have hK := paperEnrichmentFixedCost_bounds f D
  have hA := paperWalkWindow_area_log_bounds z D U g (by positivity) hstep
  have hApos : 0 < A := (mul_pos hg hU).trans_le hA.1
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hAhi : A ≤ 3 * g * U := by
    have hm := mul_le_mul_of_nonneg_right hg2 hU.le
    nlinarith [hK.2.2.1]
  have hH0 := (walkSeparationOverhead_bounds f z D (paperWalkWindow U g)).1
  have hH : walkSeparationOverhead f z D (paperWalkWindow U g) ≤ g ^ 2 * U :=
    (walkSeparationOverhead_le_fixed f z D _).trans (hK.2.1.trans hs.1)
  have hga := mul_le_mul_of_nonneg_left hA.1 hg.le
  have hsizeA : (19 + 2099520 * (f.natDegree : ℝ)) * L ≤ (8 * g) ^ 9 * A :=
    hs.2.2.trans (mul_le_mul_of_nonneg_left hA.1 (by positivity))
  have ht := separation_power_nine_quotas f.natDegree A L (8 * g) hApos.le hL.1 hL2
    (by positivity) (by linarith) hsizeA
  have hb := (paperRank_pair_bounds U L g hU hL.1 hg hg64 hs.2.1).2.2.1
  have hprefix := paper_prefix_cost_le A U L (Real.log (2 * T : ℕ))
    (2 * Real.log (4 * D + 1 : ℕ)) g (paperOutputRank U L g) hU.le hg hA.1
    (hK.2.2.2.2.trans hs.1) hb hL.2.2.2
  have hi := paper_separation_inventory A _ U L g hU hL.1 hg hg64 hA.1 hAhi hH0 hH hs.2.1 ht.1
  refine ⟨hApos, ?_, ht.1, hprefix, ht.2.1, ht.2.2, ?_⟩
  · nlinarith
  · exact hi.trans hinventory

theorem paper_enrichment_physical_quota (f : Polynomial ℤ) (D : ℕ) (U g : ℝ)
    (P : Finset ℕ) (T : ℕ) (hU : 0 < U) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hg : 0 < g) (hg64 : g < 1 / 64)
    (hsize : paperEnrichmentSizeConstant f D * primeBatchLogMean P ≤ g ^ 10 * U) :
    4 * (g * U + Real.log 2) + 4 * Real.log (4 * D + 1 : ℕ) +
      2 * (paperOutputRank U (primeBatchLogMean P) g : ℝ) * Real.log (2 * T : ℕ) ≤
      2 * (8 * g) * (paperInputRank U (primeBatchLogMean P) -
        paperOutputRank U (primeBatchLogMean P) g : ℕ) * primeBatchLogMean P := by
  let L := primeBatchLogMean P
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hL2 : Real.log 2 ≤ L :=
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT)).trans hL.2.1
  have hs := paperEnrichment_size_inputs f D U L g hU hL.1 hL2 hg (by linarith) hsize
  have hr := paperRank_pair_bounds U L g hU hL.1 hg hg64 hs.2.1
  have hp := paper_physical_cost_le U L (Real.log (2 * T : ℕ)) (paperWalkPhysicalConstant D)
    g (paperInputRank U L) (paperOutputRank U L g) hU hg hg64 hr.2.1.le hs.2.1
    ((paperEnrichmentFixedCost_bounds f D).2.2.2.1.trans hs.1) hr.2.2.2 hr.2.2.1 hL.2.2.2
  unfold paperWalkPhysicalConstant at hp
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperWalkPhysicalConstant
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentFixedCost
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSizeConstant
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentFixedCost_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichmentSizeConstant_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperEnrichment_size_inputs
#print axioms BinaryFormMoat.GeometryIntegration.paper_walk_enrichment_quota
#print axioms BinaryFormMoat.GeometryIntegration.paper_enrichment_physical_quota
