import Integrations.ConstructedSeparationError435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open HarperIntegration

def paperInputRank (U L : ℝ) : ℕ := ⌊U / L⌋₊
def paperOutputRank (U L g : ℝ) : ℕ := ⌊g ^ 2 * U / L⌋₊

theorem floorRank_log_bounds (X L : ℝ) (hX : 0 ≤ X) (hL : 0 < L) :
    (⌊X / L⌋₊ : ℝ) * L ≤ X ∧ X - L ≤ (⌊X / L⌋₊ : ℝ) * L := by
  have hf := (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg hX hL.le))
  have hc := (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (X / L))
  exact ⟨hf, by nlinarith⟩

theorem paperRank_pair_bounds (U L g : ℝ) (hU : 0 < U) (hL : 0 < L)
    (hg : 0 < g) (hg64 : g < 1 / 64) (hlarge : L ≤ g ^ 2 * U) :
    0 < paperOutputRank U L g ∧ paperOutputRank U L g < paperInputRank U L ∧
      (paperOutputRank U L g : ℝ) * L ≤ g ^ 2 * U ∧
      U - L ≤ (paperInputRank U L : ℝ) * L := by
  have hb := floorRank_log_bounds (g ^ 2 * U) L (by positivity) hL
  have hq := floorRank_log_bounds U L hU.le hL
  have hp : 0 < paperOutputRank U L g := by
    apply Nat.floor_pos.mpr
    apply (le_div_iff₀ hL).mpr
    simpa using hlarge
  have hg2 : g ^ 2 < 1 / 2 := by nlinarith
  have hm := mul_lt_mul_of_pos_right hg2 hU
  have hblt : (paperOutputRank U L g : ℝ) < paperInputRank U L := by
    apply (mul_lt_mul_iff_left₀ hL).mp
    change (⌊g ^ 2 * U / L⌋₊ : ℝ) * L < (⌊U / L⌋₊ : ℝ) * L
    nlinarith
  exact ⟨hp, by exact_mod_cast hblt, hb.1, hq.2⟩

theorem paper_prefix_cost_le (A U L V C g : ℝ) (b : ℕ)
    (hU : 0 ≤ U) (hg : 0 < g) (hA : g * U ≤ A) (hC : C ≤ g ^ 2 * U)
    (hb : (b : ℝ) * L ≤ g ^ 2 * U) (hV : V ≤ 2 * L) :
    C + 2 * (b : ℝ) * V ≤ (8 * g) * A := by
  have hba := mul_le_mul_of_nonneg_left hA hg.le
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * (b : ℝ) by positivity)
  have hn : 0 ≤ g * A := mul_nonneg hg.le ((mul_nonneg hg.le hU).trans hA)
  nlinarith

/-- The actual physical numerator fits with the internal slack 8g. -/
theorem paper_physical_cost_le (U L V C g : ℝ) (q b : ℕ)
    (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64) (hbq : b ≤ q)
    (hlarge : L ≤ g ^ 2 * U) (hC : C ≤ g ^ 2 * U)
    (hq : U - L ≤ (q : ℝ) * L) (hb : (b : ℝ) * L ≤ g ^ 2 * U)
    (hV : V ≤ 2 * L) :
    4 * g * U + C + 2 * (b : ℝ) * V ≤
      2 * (8 * g) * (q - b : ℕ) * L := by
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hg16 : g ^ 2 ≤ 1 / 16 := by nlinarith
  have hsmall := mul_le_mul_of_nonneg_right hg16 hU.le
  have hsmallg := mul_le_mul_of_nonneg_right hg2 hU.le
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * (b : ℝ) by positivity)
  have he : ((q - b : ℕ) : ℝ) * L = (q : ℝ) * L - (b : ℝ) * L := by
    rw [Nat.cast_sub hbq]
    ring
  have hdiff : 7 * U / 8 ≤ (q - b : ℕ) * L := by rw [he]; nlinarith
  have hr := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 16 * g by positivity)
  nlinarith

/-- The rounded separation subset fits inside the paper's q-b inventory.
The available batch only needs to contain q coordinates. -/
theorem paper_separation_inventory (A H U L g : ℝ)
    (hU : 0 < U) (hL : 0 < L) (hg : 0 < g) (hg64 : g < 1 / 64)
    (hA : g * U ≤ A) (hAhi : A ≤ 3 * g * U) (hH : 0 ≤ H) (hHhi : H ≤ g ^ 2 * U)
    (hlarge : L ≤ g ^ 2 * U)
    (hround : (1 + 18 / (8 * g) ^ 2) * L ≤ (8 * g) * A) :
    paperOutputRank U L g + scaledSeparationTarget A H L (8 * g) +
      2 * harperQuotaWidth (8 * g) ≤ paperInputRank U L := by
  have hga : 0 < A := (mul_pos hg hU).trans_le hA
  have hs : 0 < 8 * g := by positivity
  have hs8 : 8 * g ≤ 1 / 8 := by linarith
  have hq : 0 < harperQuotaWidth (8 * g) := by
    have h := (harperQuotaWidth_schedule _ hs).1
    omega
  have hroundq := harperQuota_rounding_cost (8 * g) L _ hs (by linarith) hL.le hround
  have hHA := mul_le_mul_of_nonneg_left hA hg.le
  have hh : H ≤ (8 * g) * A := by nlinarith
  have hcount := scaledSeparationCount_density_upper _ hq A H L (8 * g)
    hga hH hL hs.le hs8 hh hroundq
  have hr : (scaledSeparationTarget A H L (8 * g) : ℝ) ≤
      roundedHarperCount (harperQuotaWidth (8 * g)) (scaledSeparationTarget A H L (8 * g)) := by
    exact_mod_cast (roundedHarperCount_bounds _ _ hq).1
  have hrL := mul_le_mul_of_nonneg_right hr hL.le
  have hupper := mul_le_mul_of_nonneg_left hAhi
    (show 0 ≤ 1 + 56 * g by positivity)
  have hb := floorRank_log_bounds (g ^ 2 * U) L (by positivity) hL
  have hqin := floorRank_log_bounds U L hU.le hL
  have hpoly : 3 * g + 170 * g ^ 2 ≤ 1 := by nlinarith
  have hpolyU := mul_le_mul_of_nonneg_right hpoly hU.le
  have hi : ((paperOutputRank U L g + scaledSeparationTarget A H L (8 * g) +
      2 * harperQuotaWidth (8 * g) : ℕ) : ℝ) * L ≤ (paperInputRank U L : ℝ) * L := by
    push_cast
    change ((⌊g ^ 2 * U / L⌋₊ : ℝ) + _ + _) * L ≤ (⌊U / L⌋₊ : ℝ) * L
    nlinarith
  exact_mod_cast (mul_le_mul_iff_left₀ hL).mp hi

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperInputRank
#print axioms BinaryFormMoat.GeometryIntegration.paperOutputRank
#print axioms BinaryFormMoat.GeometryIntegration.floorRank_log_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperRank_pair_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paper_prefix_cost_le
#print axioms BinaryFormMoat.GeometryIntegration.paper_physical_cost_le
#print axioms BinaryFormMoat.GeometryIntegration.paper_separation_inventory
