import Moat.HammingGeometry
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

namespace BinaryFormMoat

/-- Radius-one growth for small sets iterates until the threshold is reached.
The proof tracks saturation explicitly, so it never applies a small-set
estimate after the neighborhood has already become large. -/
theorem hamming_growth_until_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (g : ℝ) (hg : 0 ≤ g) (U : ℕ)
    (hstep : ∀ B : Finset (∀ i, K i), B.card ≤ U →
      g * (B.card : ℝ) ≤ (hammingNeighborhood 1 B).card)
    (A : Finset (∀ i, K i)) (r : ℕ) :
    min (g ^ r * A.card) (U : ℝ) ≤ (hammingNeighborhood r A).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hmono : (hammingNeighborhood r A).card ≤ (hammingNeighborhood (r + 1) A).card :=
      Finset.card_le_card (hammingNeighborhood_mono_radius r (r + 1) (by omega) A)
    by_cases hbig : U ≤ (hammingNeighborhood r A).card
    · exact (min_le_right _ _).trans (by exact_mod_cast hbig.trans hmono)
    · have hsmall : (hammingNeighborhood r A).card ≤ U := by omega
      have hsmall' : ((hammingNeighborhood r A).card : ℝ) < U := by exact_mod_cast Nat.lt_of_not_ge hbig
      have hprev : g ^ r * A.card ≤ (hammingNeighborhood r A).card := by
        rcases min_le_iff.mp ih with h | h
        · exact h
        · exact (not_le_of_gt hsmall' h).elim
      apply (min_le_left _ _).trans
      calc
        _ = g * (g ^ r * A.card) := by rw [pow_succ]; ring
        _ ≤ g * (hammingNeighborhood r A).card := mul_le_mul_of_nonneg_left hprev hg
        _ ≤ (hammingNeighborhood 1 (hammingNeighborhood r A)).card := hstep _ hsmall
        _ ≤ _ := by exact_mod_cast Finset.card_le_card (hammingNeighborhood_comp_subset 1 r A)

/-- Before saturation, the full multiplicative growth factor is available. -/
theorem hamming_growth_below_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (g : ℝ) (hg : 0 ≤ g) (U : ℕ)
    (hstep : ∀ B : Finset (∀ i, K i), B.card ≤ U →
      g * (B.card : ℝ) ≤ (hammingNeighborhood 1 B).card)
    (A : Finset (∀ i, K i)) (r : ℕ) (hsmall : g ^ r * A.card ≤ U) :
    g ^ r * A.card ≤ (hammingNeighborhood r A).card := by
  simpa only [min_eq_left hsmall] using hamming_growth_until_threshold g hg U hstep A r

end BinaryFormMoat
