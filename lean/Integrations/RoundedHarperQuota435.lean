import Integrations.DifferenceSeparation435
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
namespace BinaryFormMoat.HarperIntegration

/-- Explicit integer width discharges the Harper schedule inequality. -/
def harperQuotaWidth (η : ℝ) : ℕ := max 2 ⌈6 / η ^ 2⌉₊

def roundedHarperBlocks (q r : ℕ) : ℕ := ⌈(r : ℝ) / (2 * q : ℕ)⌉₊

def roundedHarperCount (q r : ℕ) : ℕ := 2 * q * roundedHarperBlocks q r

theorem harperQuotaWidth_schedule (η : ℝ) (hη : 0 < η) :
    2 ≤ harperQuotaWidth η ∧ 3 ≤ (η ^ 2 / 2) * harperQuotaWidth η := by
  have hp : 0 < η ^ 2 := sq_pos_of_pos hη
  have hn : ⌈6 / η ^ (2 : ℕ)⌉₊ ≤ harperQuotaWidth η := le_max_right _ _
  have hc : 6 / η ^ 2 ≤ (harperQuotaWidth η : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hm := (div_le_iff₀ hp).mp hc
  constructor
  · exact le_max_left _ _
  · nlinarith

theorem harperQuotaWidth_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (harperQuotaWidth η : ℝ) ≤ 9 / η ^ 2 := by
  have hp : 0 < η ^ 2 := sq_pos_of_pos hη
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 6 / η ^ 2 by positivity)
  have hm : harperQuotaWidth η ≤ 2 + ⌈6 / η ^ 2⌉₊ := by
    unfold harperQuotaWidth
    omega
  have hmR : (harperQuotaWidth η : ℝ) ≤ 2 + (⌈6 / η ^ 2⌉₊ : ℝ) := by exact_mod_cast hm
  have hs : η ^ 2 ≤ 1 := by nlinarith
  have hh : 3 ≤ 3 / η ^ 2 := (le_div_iff₀ hp).mpr (by nlinarith)
  have he : 6 / η ^ 2 + 3 / η ^ 2 = 9 / η ^ 2 := by ring
  linarith

/-- Integer rounding changes the target count by strictly less than one block. -/
theorem roundedHarperCount_bounds (q r : ℕ) (hq : 0 < q) :
    r ≤ roundedHarperCount q r ∧ roundedHarperCount q r < r + 2 * q := by
  have hd : (0 : ℝ) < (2 * q : ℕ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hl := Nat.le_ceil ((r : ℝ) / (2 * q : ℕ))
  have hu := Nat.ceil_lt_add_one (show 0 ≤ (r : ℝ) / (2 * q : ℕ) by positivity)
  have hl' := (div_le_iff₀ hd).mp hl
  have hu' := mul_lt_mul_of_pos_right hu hd
  rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at hu'
  have hlR : (r : ℝ) ≤ (roundedHarperCount q r : ℝ) := by
    simpa only [roundedHarperCount, roundedHarperBlocks, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm] using hl'
  have huR : (roundedHarperCount q r : ℝ) < (r + 2 * q : ℕ) := by
    simpa only [roundedHarperCount, roundedHarperBlocks, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat, mul_comm] using hu'
  constructor
  · exact_mod_cast hlR
  · exact_mod_cast huR

theorem roundedHarperBlocks_pos (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    1 ≤ roundedHarperBlocks q r := by
  unfold roundedHarperBlocks
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (by exact_mod_cast hr) (by exact_mod_cast (by omega : 0 < 2 * q))

theorem roundedHarperCount_fits (q r available : ℕ) (hq : 0 < q)
    (hbudget : r + 2 * q ≤ available) : roundedHarperCount q r ≤ available :=
  (Nat.le_of_lt (roundedHarperCount_bounds q r hq).2).trans hbudget

/-- The coarser binary encoding still gives an explicit eta^8 exponential rate.
This is a scalar tail comparison; determinant/product and log-gap inputs remain. -/
theorem roundedHarper_exp_tail_le (d q r : ℕ) (hd : 1 ≤ d) (hq : 0 < q)
    (η : ℝ) (hη : 0 < η) (hwidth : (q : ℝ) ≤ 9 / η ^ 2) :
    let w := 16 * d * q ^ 2 + 4
    Real.exp (-(roundedHarperBlocks q r : ℝ) / (4 * (w * q : ℕ))) ≤
      Real.exp (-(η ^ 8 * r) / (1049760 * d)) := by
  let w := 16 * d * q ^ 2 + 4
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hwR : (w : ℝ) = 16 * d * (q : ℝ) ^ 2 + 4 := by
    dsimp only [w]
    push_cast
    rfl
  have hwb : (w : ℝ) ≤ 20 * d * (q : ℝ) ^ 2 := by
    rw [hwR]
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hq2 (show (0 : ℝ) ≤ d by positivity)
    have hmul : (1 : ℝ) ≤ (d : ℝ) * (q : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hpow : (q : ℝ) ^ 4 ≤ (9 / η ^ 2) ^ 4 := by gcongr
  have hrate : η ^ 8 * (q : ℝ) ^ 4 ≤ 6561 := by
    calc
      _ ≤ η ^ 8 * (9 / η ^ 2) ^ 4 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 6561 := by field_simp; ring
  have hden : η ^ 8 * (8 * (w : ℝ) * (q : ℝ) ^ 2) ≤ 1049760 * d := by
    calc
      _ ≤ η ^ 8 * (8 * (20 * d * (q : ℝ) ^ 2) * (q : ℝ) ^ 2) := by gcongr
      _ = (160 * d) * (η ^ 8 * (q : ℝ) ^ 4) := by ring
      _ ≤ (160 * d) * 6561 := by gcongr
      _ = _ := by ring
  have hc : (r : ℝ) ≤ 2 * q * (roundedHarperBlocks q r : ℝ) := by
    exact_mod_cast (roundedHarperCount_bounds q r hq).1
  have hwpos : (0 : ℝ) < w := by rw [hwR]; positivity
  change Real.exp (-(roundedHarperBlocks q r : ℝ) / (4 * (w * q : ℕ))) ≤ _
  simp only [neg_div]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  rw [Nat.cast_mul]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1049760 * d)
    (by positivity : (0 : ℝ) < 4 * ((w : ℝ) * q))).mpr
  calc
    _ ≤ (η ^ 8 * (2 * q * (roundedHarperBlocks q r : ℝ))) * (4 * ((w : ℝ) * q)) := by gcongr
    _ = (roundedHarperBlocks q r : ℝ) * (η ^ 8 * (8 * (w : ℝ) * (q : ℝ) ^ 2)) := by ring
    _ ≤ _ := by gcongr

theorem harperQuota_rounded_exp_rate (d r : ℕ) (hd : 1 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    let q := harperQuotaWidth η
    let w := 16 * d * q ^ 2 + 4
    Real.exp (-(roundedHarperBlocks q r : ℝ) / (4 * (w * q : ℕ))) ≤
      Real.exp (-(η ^ 8 * r) / (1049760 * d)) := by
  apply roundedHarper_exp_tail_le d (harperQuotaWidth η) r hd
    (by have h := (harperQuotaWidth_schedule η hη).1; omega) η hη
    (harperQuotaWidth_le η hη hη1)

end BinaryFormMoat.HarperIntegration

namespace BinaryFormMoat.GeometryIntegration
open HarperIntegration

/-- Actual walk separation with constructed rounded width and an explicit
eta^8 rate. Prime-product and radius log-gap inequalities remain arithmetic inputs. -/
theorem walk_difference_separation_rounded_rate (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (r : ℕ) (hr : 0 < r) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcount : P.card = roundedHarperCount (harperQuotaWidth η) r)
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T)
    (hgap : Real.log (max 1 (4 * (D * N)) : ℕ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : (16 * prefixArea z N) *
      (2 * T) ^ (2 * roundedHarperBlocks (harperQuotaWidth η) r) < ∏ p ∈ P, p) :
    ((nonInjectiveRootAssignments (pointDifferences (walkVertexSet z N)) P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) ≤ Real.exp (-(η ^ 8 * r) / (1049760 * f.natDegree)) := by
  have hq : 0 < harperQuotaWidth η := by
    have h := (harperQuotaWidth_schedule η hη).1
    omega
  have h := walk_difference_separation_exp_tail f hf hd z D N hstep P hP S hcard hroot
    (harperQuotaWidth η) (roundedHarperBlocks (harperQuotaWidth η) r) hq
    (roundedHarperBlocks_pos _ r hq hr) hcount T hT hpT η hη.le
    (harperQuotaWidth_schedule η hη).2 hgap hlarge
  exact h.trans (harperQuota_rounded_exp_rate f.natDegree r (by omega) η hη hη1)

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.HarperIntegration.harperQuotaWidth
#print axioms BinaryFormMoat.HarperIntegration.roundedHarperBlocks
#print axioms BinaryFormMoat.HarperIntegration.roundedHarperCount
#print axioms BinaryFormMoat.HarperIntegration.harperQuotaWidth_schedule
#print axioms BinaryFormMoat.HarperIntegration.harperQuotaWidth_le
#print axioms BinaryFormMoat.HarperIntegration.roundedHarperCount_bounds
#print axioms BinaryFormMoat.HarperIntegration.roundedHarperBlocks_pos
#print axioms BinaryFormMoat.HarperIntegration.roundedHarperCount_fits
#print axioms BinaryFormMoat.HarperIntegration.roundedHarper_exp_tail_le
#print axioms BinaryFormMoat.HarperIntegration.harperQuota_rounded_exp_rate
#print axioms BinaryFormMoat.GeometryIntegration.walk_difference_separation_rounded_rate
