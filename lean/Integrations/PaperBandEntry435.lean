import Integrations.PaperBandIteration435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration

/-- Construct the first geometric-grid scale at most the target V. -/
def paperBandEntry (hi g V : ℝ) : ℕ := ⌈(hi - Real.log V) / paperBandLogStep g⌉₊

theorem paperBandLogStep_eq_neg_log (g : ℝ) (hg : 0 < g) :
    paperBandLogStep g = -2 * Real.log g := by
  unfold paperBandLogStep
  rw [Real.log_div (by norm_num) hg.ne', Real.log_one]
  ring

/-- The ceiling loses less than one grid step. -/
theorem paperBandEntry_log_bounds (hi g V : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hhi : Real.log V ≤ hi) :
    Real.log V - paperBandLogStep g <
        Real.log (paperBandScale (Real.exp hi) g (paperBandEntry hi g V)) ∧
      Real.log (paperBandScale (Real.exp hi) g (paperBandEntry hi g V)) ≤ Real.log V := by
  have hs := paperBandLogStep_pos g hg hg1
  have hr : 0 ≤ (hi - Real.log V) / paperBandLogStep g := div_nonneg (sub_nonneg.mpr hhi) hs.le
  have hlo := (div_le_iff₀ hs).mp (Nat.le_ceil ((hi - Real.log V) / paperBandLogStep g))
  have hupper := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hr) hs
  rw [add_mul, div_mul_cancel₀ _ hs.ne'] at hupper
  rw [paperBandScale_log _ _ (Real.exp_pos _) hg, Real.log_exp]
  dsimp [paperBandEntry] at *
  simp only [paperBandLogStep_eq_neg_log g hg] at hlo hupper ⊢
  constructor <;> nlinarith

theorem paperBandEntry_scale_bounds (hi g V : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hV : 0 < V) (hhi : Real.log V ≤ hi) :
    g ^ 2 * V < paperBandScale (Real.exp hi) g (paperBandEntry hi g V) ∧
      paperBandScale (Real.exp hi) g (paperBandEntry hi g V) ≤ V := by
  have hb := paperBandEntry_log_bounds hi g V hg hg1 hhi
  have hp := paperBandScale_pos (Real.exp hi) g (Real.exp_pos _) hg (paperBandEntry hi g V)
  have he : Real.log (g ^ 2 * V) = Real.log V - paperBandLogStep g := by
    rw [Real.log_mul (by positivity) hV.ne', Real.log_pow, paperBandLogStep_eq_neg_log g hg]
    ring
  exact ⟨(Real.log_lt_log_iff (by positivity) hp).mp (he.symm ▸ hb.1),
    (Real.log_le_log_iff hp hV).mp hb.2⟩

theorem paperBandScale_add (U g : ℝ) (n l : ℕ) :
    paperBandScale U g (n + l) = paperBandScale (paperBandScale U g n) g l := by
  unfold paperBandScale
  rw [pow_add]
  ring

/-- A block of l transitions and its recording scale really fit in the band.
The margin explicitly includes the one ceiling grid step. -/
theorem paperBandEntry_block_fits (lo hi g V : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hhi : Real.log V ≤ hi) (l : ℕ)
    (hroom : lo + ((l : ℝ) + 1) * paperBandLogStep g ≤ Real.log V) :
    paperBandEntry hi g V + l < paperBandLength lo hi g := by
  have hs := paperBandLogStep_pos g hg hg1
  have hb := (paperBandEntry_log_bounds hi g V hg hg1 hhi).1
  have he : Real.log (paperBandScale (Real.exp hi) g (paperBandEntry hi g V)) =
      hi - (paperBandEntry hi g V : ℝ) * paperBandLogStep g := by
    rw [paperBandScale_log _ _ (Real.exp_pos _) hg, Real.log_exp, paperBandLogStep_eq_neg_log g hg]
    ring
  rw [he] at hb
  have hn : ((paperBandEntry hi g V + l : ℕ) : ℝ) ≤ (hi - lo) / paperBandLogStep g := by
    apply (le_div_iff₀ hs).mpr
    push_cast
    nlinarith
  have hf : paperBandEntry hi g V + l ≤ ⌊(hi - lo) / paperBandLogStep g⌋₊ :=
    Nat.le_floor hn
  unfold paperBandLength
  omega

theorem paperBandEntry_record_scale_bounds (hi g V : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hV : 0 < V) (hhi : Real.log V ≤ hi) (l : ℕ) :
    (g ^ 2) ^ (l + 1) * V <
        paperBandScale (Real.exp hi) g (paperBandEntry hi g V + l) ∧
      paperBandScale (Real.exp hi) g (paperBandEntry hi g V + l) ≤ (g ^ 2) ^ l * V := by
  have hb := paperBandEntry_scale_bounds hi g V hg hg1 hV hhi
  rw [paperBandScale_add]
  change (g ^ 2) ^ (l + 1) * V <
      (g ^ 2) ^ l * paperBandScale (Real.exp hi) g (paperBandEntry hi g V) ∧
    (g ^ 2) ^ l * paperBandScale (Real.exp hi) g (paperBandEntry hi g V) ≤ (g ^ 2) ^ l * V
  constructor
  · calc
      _ = (g ^ 2) ^ l * (g ^ 2 * V) := by rw [pow_succ]; ring
      _ < _ := mul_lt_mul_of_pos_left hb.1 (pow_pos (sq_pos_of_pos hg) l)
  · exact mul_le_mul_of_nonneg_left hb.2 (pow_nonneg (sq_nonneg g) l)

/-- Integer recording loses at most L; the reserved half-scale margin gives
the positive linear entropy mass used by the top-band argument. -/
theorem paperBandEntry_record_rank_mass (hi g V L : ℝ) (hg : 0 < g) (hg1 : g < 1)
    (hV : 0 < V) (hhi : Real.log V ≤ hi) (hL : 0 < L) (l : ℕ)
    (hsmall : L ≤ ((g ^ 2) ^ (l + 1) * V) / 2) :
    ((g ^ 2) ^ (l + 1) * V) / 2 ≤
      (paperInputRank (paperBandScale (Real.exp hi) g (paperBandEntry hi g V + l)) L : ℝ) * L := by
  have hb := (paperBandEntry_record_scale_bounds hi g V hg hg1 hV hhi l).1
  have hf := (floorRank_log_bounds (paperBandScale (Real.exp hi) g (paperBandEntry hi g V + l))
    L (paperBandScale_pos (Real.exp hi) g (Real.exp_pos hi) hg (paperBandEntry hi g V + l)).le hL).2
  change _ ≤ (⌊paperBandScale (Real.exp hi) g (paperBandEntry hi g V + l) / L⌋₊ : ℝ) * L
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry
#print axioms BinaryFormMoat.GeometryIntegration.paperBandLogStep_eq_neg_log
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_log_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_scale_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandScale_add
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_block_fits
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_record_scale_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperBandEntry_record_rank_mass
