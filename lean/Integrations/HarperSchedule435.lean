import Integrations.HarperThreshold435
import Moat.ExpansionParameters

namespace BinaryFormMoat.HarperIntegration

/-- An exact-multiple schedule discharges the scalar logarithmic budget.
The dimension is 2*m*l, the root tail uses k=2*q*l, and the radius is l.
No floor approximation and no hidden large-l assumption is used. -/
theorem scheduled_harper_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q l : ℕ) (hm : 2 ≤ m) (hl : 1 ≤ l)
    (hdim : Fintype.card ι = 2 * m * l) (a : ℝ) (haq : 3 ≤ a * q)
    (A : Finset (ι → Bool))
    (hA : (A.card : ℝ) / 2 ^ Fintype.card ι ≤ Real.exp (-a * (2 * q * l))) :
    ((((m : ℝ) + 1) * l) / (((m : ℝ) - 1) * l + 1)) ^ l * A.card ≤
      (hammingNeighborhood l A).card := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨ht, hdiff⟩ := scheduled_cutoff_arithmetic m l hm1
  have ht' : 2 * ((m - 1) * l) ≤ Fintype.card ι := by rwa [hdim]
  have hfactor : ((Fintype.card ι - (m - 1) * l : ℕ) : ℝ) /
      (((m - 1) * l : ℕ) + 1) =
        (((m : ℝ) + 1) * l) / (((m : ℝ) - 1) * l + 1) := by
    rw [hdim, hdiff]
    push_cast [Nat.cast_sub hm1]
    rfl
  have hpos : 0 < (((m : ℝ) + 1) * l) / (((m : ℝ) - 1) * l + 1) := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h := (scheduled_factor_bounds (m : ℝ) l hm' hl').1
    have : 0 < 1 + 1 / (m : ℝ) := by positivity
    exact this.trans_le h
  have hbudget := scheduled_log_budget (m : ℝ) l q a
    (by exact_mod_cast hm) (by exact_mod_cast hl) haq
  have hcoef : (Fintype.card ι : ℝ) - 2 * ((m - 1) * l : ℕ) + 1 = 2 * l + 1 := by
    rw [hdim]
    push_cast [Nat.cast_sub hm1]
    ring
  have h := harper_expansion_of_log ((m - 1) * l) l (2 * q * l) ht' a
    (by rw [hfactor]; exact hpos) ?_ A ?_
  · simpa only [hfactor] using h
  · rw [hfactor, hcoef]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hA

end BinaryFormMoat.HarperIntegration
