import Moat.ExpansionBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace BinaryFormMoat

/-- A coarse logarithmic bound sufficient for a schedule of cube dimensions.
Keeping the factor's dependence on the block size prevents a circular choice. -/
theorem log_one_add_inv_lower (m : ℝ) (hm : 1 ≤ m) :
    1 / (2 * m) ≤ Real.log (1 + 1 / m) := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < 1 + 1 / m := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1 + 1 / m)⁻¹ = 1 / (m + 1) := by field_simp; ring
  rw [he] at hlog
  exact (one_div_le_one_div_of_le (by positivity : 0 < m + 1) (by linarith)).trans hlog

/-- For dimensions n=2*m*l and cutoff t=(m-1)*l, the cube growth factor is
bounded uniformly in the scale l, with the m dependence explicit. -/
theorem scheduled_factor_bounds (m l : ℝ) (hm : 2 ≤ m) (hl : 1 ≤ l) :
    1 + 1 / m ≤ ((m + 1) * l) / ((m - 1) * l + 1) ∧
      ((m + 1) * l) / ((m - 1) * l + 1) ≤ 3 := by
  have hm0 : 0 < m := by linarith
  have hden : 0 < (m - 1) * l + 1 := by
    have := mul_nonneg (show 0 ≤ m - 1 by linarith) (show 0 ≤ l by linarith)
    linarith
  constructor
  · apply (le_div_iff₀ hden).mpr
    have he : (1 + 1 / m) * ((m - 1) * l + 1) =
        ((m + 1) * ((m - 1) * l + 1)) / m := by field_simp
    rw [he]
    apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_nonneg (show 0 ≤ m + 1 by linarith) (show 0 ≤ l - 1 by linarith)]
  · apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (show 0 ≤ m - 2 by linarith) (show 0 ≤ l by linarith)]

theorem scheduled_factor_log_bounds (m l : ℝ) (hm : 2 ≤ m) (hl : 1 ≤ l) :
    1 / (2 * m) ≤ Real.log (((m + 1) * l) / ((m - 1) * l + 1)) ∧
      Real.log (((m + 1) * l) / ((m - 1) * l + 1)) ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := scheduled_factor_bounds m l hm hl
  have hp : 0 < 1 + 1 / m := by positivity
  have hg := hp.trans_le hlo
  exact ⟨(log_one_add_inv_lower m (by linarith)).trans (Real.log_le_log hp hlo),
    (Real.log_le_sub_one_of_pos hg).trans (by linarith)⟩

/-- The logarithmic size budget closes with a deliberately coarse constant.
There is no asymptotic threshold in this inequality. -/
theorem scheduled_log_budget (m l q a : ℝ) (hm : 2 ≤ m) (hl : 1 ≤ l)
    (haq : 3 ≤ a * q) :
    l * Real.log (((m + 1) * l) / ((m - 1) * l + 1)) +
      (2 * l + 1) * Real.log 2 ≤ a * (2 * q * l) := by
  have hlog := (scheduled_factor_log_bounds m l hm hl).2
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ l by linarith)
  have h2 := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 2 * l + 1 by linarith)
  have h3 := mul_le_mul_of_nonneg_right haq (show 0 ≤ l by linarith)
  nlinarith

/-- Choosing the block size so Q>=16*d*m*q leaves a definite expansion rate
after exact-balancing losses. Later m=b*q and Q=2^b. -/
theorem scheduled_net_gain (m l d q Q : ℝ) (hm : 2 ≤ m) (hl : 1 ≤ l)
    (hd : 0 < d) (hq : 0 < q) (hQ : 16 * d * m * q ≤ Q) :
    l / (4 * m) ≤
      l * Real.log (((m + 1) * l) / ((m - 1) * l + 1)) - 2 * d / Q * (2 * q * l) := by
  have hm0 : 0 < m := by linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hl0 : 0 ≤ l := by linarith
  have hlog := mul_le_mul_of_nonneg_left (scheduled_factor_log_bounds m l hm hl).1 hl0
  have hcost : 2 * d / Q * (2 * q * l) ≤ l / (4 * m) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * m)).mpr
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ hQ0).mpr
    have h := mul_le_mul_of_nonneg_right hQ hl0
    nlinarith only [h]
  have he : l * (1 / (2 * m)) = l / (4 * m) + l / (4 * m) := by field_simp; ring
  rw [he] at hlog
  linarith

/-- A coarse elementary domination is enough to choose the binary block
length; no new limit or effective prime-counting estimate is needed. -/
theorem square_le_two_pow (b : ℕ) (hb : 4 ≤ b) : b ^ 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    rw [pow_succ 2 b]
    nlinarith

/-- A concrete block width, deliberately far from optimal, simultaneously
controls the dimension-dependent growth loss and the balancing cost. -/
theorem explicit_balanced_growth_block (d q : ℕ) (hq : 0 < q) :
    let b := 16 * d * q ^ 2 + 4
    2 ≤ b * q ∧ 2 * d ≤ 2 ^ b ∧ 16 * d * (b * q) * q ≤ 2 ^ b := by
  dsimp
  set b := 16 * d * q ^ 2 + 4 with hb
  have hb4 : 4 ≤ b := by omega
  have hbq : 2 ≤ b * q := by nlinarith
  have hsq := square_le_two_pow b hb4
  have hbig : 16 * d * (b * q) * q ≤ 2 ^ b := by
    calc
      _ = (16 * d * q ^ 2) * b := by ring
      _ ≤ b * b := Nat.mul_le_mul_right b (by omega)
      _ = b ^ 2 := by ring
      _ ≤ _ := hsq
  refine ⟨hbq, ?_, hbig⟩
  have hleft : 2 * d ≤ 16 * d * (b * q) * q := by
    calc
      2 * d ≤ (b * q) * d := Nat.mul_le_mul_right d hbq
      _ ≤ 16 * ((b * q) * d) := Nat.le_mul_of_pos_left _ (by decide)
      _ = 16 * d * (b * q) := by ring
      _ ≤ _ := Nat.le_mul_of_pos_right _ hq
  exact hleft.trans hbig

/-- The schedule can use an integer tail parameter at every positive tail rate. -/
theorem exists_integer_tail_budget (a : ℝ) (ha : 0 < a) :
    ∃ q : ℕ, 0 < q ∧ 3 ≤ a * q := by
  obtain ⟨q, hq⟩ := exists_nat_gt (3 / a)
  have hqpos : 0 < (q : ℝ) := (by positivity : (0 : ℝ) < 3 / a).trans hq
  have h := (div_lt_iff₀ ha).mp hq
  exact ⟨q, by exact_mod_cast hqpos, by nlinarith⟩

/-- The integral schedule uses exact multiples and thus avoids floor errors. -/
theorem scheduled_cutoff_arithmetic (m l : ℕ) (hm : 1 ≤ m) :
    2 * ((m - 1) * l) ≤ 2 * m * l ∧
      2 * m * l - (m - 1) * l = (m + 1) * l := by
  have he : (m - 1) * l + l = m * l := by
    calc
      _ = (m - 1 + 1) * l := by ring
      _ = _ := by rw [Nat.sub_add_cancel hm]
  have he2 : 2 * m * l = m * l + m * l := by ring
  have he3 : (m + 1) * l = m * l + l := by ring
  omega

end BinaryFormMoat
