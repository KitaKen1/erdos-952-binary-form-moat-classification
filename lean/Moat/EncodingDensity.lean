import Moat.BalancedEncoding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace BinaryFormMoat

/-- A simple lower bound sufficient for the acceptance cost; sharp constants
are unnecessary when the block length can be chosen after the degree. -/
theorem exp_neg_two_le_one_sub (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  apply (Real.le_log_iff_exp_le hp).mp
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hp)
  have he : (1 - x)⁻¹ * (1 - x) = 1 := inv_mul_cancel₀ hp.ne'
  have hm := mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)
  nlinarith

/-- Exact balancing in a Q-letter ambient alphabet loses at most exp(2dk/Q)
when conditioning on acceptance in k coordinates. -/
theorem balanced_acceptance_exp_lower (d Q k : ℕ) (hd : 0 < d) (hQ : 2 * d ≤ Q) :
    Real.exp (-2 * (d : ℝ) / Q * k) ≤
      (((d * (Q / d) : ℕ) : ℝ) / Q) ^ k := by
  have hQpos : 0 < Q := by omega
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hx : (d : ℝ) / Q ≤ 1 / 2 := by
    apply (div_le_iff₀ hQ').mpr
    have : (2 : ℝ) * d ≤ Q := by exact_mod_cast hQ
    linarith
  have hbase := (exp_neg_two_le_one_sub ((d : ℝ) / Q) (by positivity) hx).trans
    (balanced_block_fraction_lower d Q hd hQpos)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) hbase k
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

/-- The binary realization of the preceding acceptance bound. -/
theorem binary_acceptance_exp_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] (d b : ℕ)
    (hd : 0 < d) (hb : 2 * d ≤ 2 ^ b) (hK : ∀ i, Fintype.card (K i) = d)
    (e : ∀ i, K i × Fin (2 ^ b / d) ↪ (Fin b → Bool)) :
    Real.exp (-2 * (d : ℝ) / 2 ^ b * Fintype.card ι) ≤
      ((encodedEvent e Finset.univ).card : ℝ) / Fintype.card (ι → Fin b → Bool) := by
  rw [binary_acceptance_fraction d b _ hK]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    balanced_acceptance_exp_lower d (2 ^ b) (Fintype.card ι) hd hb

end BinaryFormMoat
