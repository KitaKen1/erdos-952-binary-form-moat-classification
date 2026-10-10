import Integrations.SubsetSecondMoment435
import Integrations.DyadicDifferenceSeparation435

noncomputable section

namespace BinaryFormMoat.EntropyIntegration

/-- The true prime-log mean is retained even when g*log(T) tends to zero.
The source is the uniform subset of distinct primes, not independent trials. -/
theorem powersetCard_prime_log_lower_tail (P : Finset ℕ) (T s : ℕ)
    (hT : 2 ≤ T) (hs : 2 ≤ s) (hsk : s ≤ P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (g : ℝ) (hg : 0 < g) :
    let L : ℝ := (∑ p : P, Real.log (p.val : ℝ)) / P.card
    ((((Finset.univ : Finset P).powersetCard s).filter
      (fun A => (∑ p ∈ A, Real.log (p.val : ℝ)) ≤ (1 - g) * s * L)).card : ℝ) /
      ((Finset.univ : Finset P).powersetCard s).card ≤
        (Real.log 2) ^ 2 / (g ^ 2 * s * L ^ 2) := by
  let w : P → ℝ := fun p => Real.log (p.val : ℝ)
  let L : ℝ := (∑ p : P, w p) / P.card
  have hsk' : s ≤ Fintype.card P := by simpa using hsk
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hlogs : ∀ p : P, Real.log (T : ℝ) ≤ w p ∧ w p ≤ Real.log (T : ℝ) + Real.log 2 := by
    intro p
    constructor
    · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < T))
        (by exact_mod_cast hlo p.val p.property)
    · have h : Real.log (p.val : ℝ) ≤ Real.log ((2 * T : ℕ) : ℝ) := Real.log_le_log
        (by exact_mod_cast ((by omega : 0 < T).trans_le (hlo p.val p.property)))
        (by exact_mod_cast hhi p.val p.property)
      have he : Real.log ((2 * T : ℕ) : ℝ) = Real.log (T : ℝ) + Real.log 2 := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num)
          (by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < T)))]
        ring
      simpa only [w, he] using h
  have hmean := finite_real_mean_bounds (ι := P) (by simpa using (by omega : 0 < P.card))
    w (Real.log (T : ℝ)) (Real.log (T : ℝ) + Real.log 2) hlogs
  have hL : 0 < L := by
    have h := hlogT.trans_le hmean.1
    simpa [L] using h
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have ha : 0 < g * s * L := mul_pos (mul_pos hg hsR) hL
  have ht := powersetCard_interval_lower_tail_fraction s hs hsk' w
    (Real.log (T : ℝ)) (Real.log (T : ℝ) + Real.log 2)
    (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]) hlogs
    (g * s * L) ha
  have he : (s : ℝ) * ((∑ p : P, w p) / Fintype.card P) - g * s * L =
      (1 - g) * s * L := by simp only [Fintype.card_coe]; dsimp [L]; ring
  rw [he] at ht
  change _ ≤ (Real.log 2) ^ 2 / (g ^ 2 * s * L ^ 2)
  calc
    _ ≤ (s : ℝ) * (Real.log 2) ^ 2 / (g * s * L) ^ 2 := by
      simpa only [w, add_sub_cancel_left] using ht
    _ = _ := by
      field_simp

/-- Adding uniform root labels does not change this prime-only failure fraction.
Labels are averaged outside the residue entropy experiment. -/
theorem subsetLabelAverage_prime_log_failure_le {R : Type*} [Fintype R] [Nonempty R]
    (P : Finset ℕ) (T s : ℕ) (hT : 2 ≤ T) (hs : 2 ≤ s) (hsk : s ≤ P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (g : ℝ) (hg : 0 < g) :
    let L : ℝ := (∑ p : P, Real.log (p.val : ℝ)) / P.card
    subsetLabelAverage (ι := P) (R := R) s (fun A _ =>
      if (∑ p ∈ A, Real.log (p.val : ℝ)) ≤ (1 - g) * s * L then 1 else 0) ≤
        (Real.log 2) ^ 2 / (g ^ 2 * s * L ^ 2) := by
  classical
  let : DecidableEq P := Classical.decEq P
  dsimp only
  have hQ : (Fintype.card (P → R) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcollapse (f : Finset P → ℝ) :
      subsetLabelAverage (ι := P) (R := R) s (fun A _ => f A) =
        (∑ A ∈ (Finset.univ : Finset P).powersetCard s, f A) /
          ((Finset.univ : Finset P).powersetCard s).card := by
    have hinner (A : Finset P) :
        (∑ _ρ : P → R, f A) / (Fintype.card (P → R) : ℝ) = f A := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ (f A) hQ
    unfold subsetLabelAverage
    congr 1
    exact Finset.sum_congr rfl (fun A _ => hinner A)
  rw [hcollapse]
  rw [← Finset.sum_filter]
  simpa using powersetCard_prime_log_lower_tail P T s hT hs hsk hlo hhi g hg

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.powersetCard_prime_log_lower_tail
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_prime_log_failure_le
