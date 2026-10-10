import Integrations.PrimeWordBudget435
import Integrations.TerminalSmoothing435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory
open scoped Classical

/-- A length-L word meets the time event at one of its actual offsets. -/
def eventWordHit (E : Set ℕ) (L : ℕ) : Set ℕ :=
  ⋃ i : Fin L, (fun t => t + i.val) ⁻¹' E

theorem mem_eventWordHit (E : Set ℕ) (L t : ℕ) :
    t ∈ eventWordHit E L ↔ ∃ i : Fin L, t + i.val ∈ E := by
  simp [eventWordHit]

theorem eventWordHit_probability_le (ν : Measure ℕ) (E : Set ℕ) (L : ℕ) (η : ℝ)
    (hshift : ∀ i : Fin L, ν.real ((fun t => t + i.val) ⁻¹' E) ≤ ν.real E + η) :
    ν.real (eventWordHit E L) ≤ (L : ℝ) * (ν.real E + η) := by
  have h := (measureReal_iUnion_fintype_le (μ := ν)
    (fun i : Fin L => (fun t => t + i.val) ⁻¹' E)).trans
      (Finset.sum_le_sum (fun i _ => hshift i))
  simpa only [eventWordHit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem normalized_eventWordHit_probability_le (ν : Measure ℕ) (E : Set ℕ)
    (L : ℕ) (hL : 0 < L) (η : ℝ)
    (hshift : ∀ i : Fin L, ν.real ((fun t => t + i.val) ⁻¹' E) ≤ ν.real E + η) :
    ν.real (eventWordHit E L) / L ≤ ν.real E + η := by
  apply (div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  simpa only [mul_comm] using eventWordHit_probability_le ν E L η hshift

/-- Varying positive word lengths are allowed. The common law is fixed,
and P is a set of distinct indices, not a multiset of root labels. -/
theorem sum_normalized_eventWordHit_probability_le {ι : Type*} [DecidableEq ι]
    (ν : Measure ℕ) [IsProbabilityMeasure ν] (P : Finset ι) (E : ι → Set ℕ)
    (L : ι → ℕ) (hL : ∀ p ∈ P, 0 < L p) (r : ℕ) (η : ℝ)
    (hcount : ∀ t, (P.filter (fun p => t ∈ E p)).card ≤ r)
    (hshift : ∀ p ∈ P, ∀ i : Fin (L p),
      ν.real ((fun t => t + i.val) ⁻¹' E p) ≤ ν.real (E p) + η) :
    ∑ p ∈ P, ν.real (eventWordHit (E p) (L p)) / L p ≤ r + P.card * η := by
  calc
    _ ≤ ∑ p ∈ P, (ν.real (E p) + η) := Finset.sum_le_sum (fun p hp =>
      normalized_eventWordHit_probability_le ν (E p) (L p) (hL p hp) η (hshift p hp))
    _ = (∑ p ∈ P, ν.real (E p)) + P.card * η := by simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (sum_hit_probability_le_of_count ν P
      (fun p t => t ∈ E p) r hcount) (le_refl _)

theorem sum_weighted_normalized_eventWordHit_probability_le {ι : Type*} [DecidableEq ι]
    (ν : Measure ℕ) [IsProbabilityMeasure ν] (P : Finset ι) (E : ι → Set ℕ)
    (L : ι → ℕ) (hL : ∀ p ∈ P, 0 < L p) (r : ℕ) (η : ℝ)
    (hcount : ∀ t, (P.filter (fun p => t ∈ E p)).card ≤ r)
    (hshift : ∀ p ∈ P, ∀ i : Fin (L p),
      ν.real ((fun t => t + i.val) ⁻¹' E p) ≤ ν.real (E p) + η)
    (w : ι → ℝ) (D : ℝ) (hD : 0 ≤ D) (hw : ∀ p ∈ P, w p ≤ D) :
    ∑ p ∈ P, (ν.real (eventWordHit (E p) (L p)) / L p) * w p ≤
      D * (r + P.card * η) := by
  calc
    _ ≤ ∑ p ∈ P, (ν.real (eventWordHit (E p) (L p)) / L p) * D :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hw p hp)
        (div_nonneg measureReal_nonneg (Nat.cast_nonneg _)))
    _ = D * ∑ p ∈ P, ν.real (eventWordHit (E p) (L p)) / L p := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_normalized_eventWordHit_probability_le ν P E L hL r η hcount hshift) hD

section Smoothed
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

theorem smoothedTimeLaw_event_shift_upper (E : Set ℕ) (a A : ℕ) (ha : a ≤ A) :
    (smoothedTimeLaw μ b N).real ((fun t => t + a) ⁻¹' E) ≤
      (smoothedTimeLaw μ b N).real E + (A : ℝ) / N := by
  have h := (abs_le.mp (smoothedTimeLaw_shift_event_bound μ b N E a)).2
  have he : (a : ℝ) / N ≤ (A : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha) (Nat.cast_nonneg _)
  linarith

/-- The true-value error charge for distinct rational primes, normalized
by each word's own length, has a single common-law upper budget. -/
theorem smoothedTimeLaw_root_word_error_budget
    (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (p : ℕ) → Finset (ZMod p))
    (hQ : ∀ p ∈ P, ∀ ρ ∈ Q p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (L : ℕ → ℕ) (A r U : ℕ)
    (hL : ∀ p ∈ P, 0 < L p) (hA : ∀ p ∈ P, L p ≤ A) (hU : ∀ p ∈ P, p ≤ U)
    (hz : ∀ t, value (f.homogenize n) (z t) ≠ 0)
    (hr : ∀ t, omega (value (f.homogenize n) (z t)) ≤ r) :
    ∑ p ∈ P, ((smoothedTimeLaw μ b N).real
      {t | ∃ i : Fin (L p), rootPrimeHit p Q (z (t + i))} / L p) * Real.log p ≤
      Real.log U * (r + P.card * ((A : ℝ) / N)) := by
  have hcount (t : ℕ) : (P.filter (fun p => rootPrimeHit p Q (z t))).card ≤ r :=
    (rootPrimeHit_count_le f n hn P hP Q hQ _ (hz t)).trans (hr t)
  have h := sum_weighted_normalized_eventWordHit_probability_le
    (smoothedTimeLaw μ b N) P (fun p => {t | rootPrimeHit p Q (z t)}) L hL r
    ((A : ℝ) / N) hcount
    (fun p hp i => smoothedTimeLaw_event_shift_upper μ b N _ i A
      (Nat.le_trans (Nat.le_of_lt i.isLt) (hA p hp)))
    (fun p => Real.log p) (Real.log U) (Real.log_natCast_nonneg _)
    (fun p hp => Real.log_le_log (by exact_mod_cast (hP p hp).pos)
      (by exact_mod_cast hU p hp))
  have he (p : ℕ) : eventWordHit {t | rootPrimeHit p Q (z t)} (L p) =
      {t | ∃ i : Fin (L p), rootPrimeHit p Q (z (t + i))} := by
    ext t
    exact mem_eventWordHit _ _ _
  simpa only [he] using h

end Smoothed
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mem_eventWordHit
#print axioms BinaryFormMoat.EntropyIntegration.eventWordHit_probability_le
#print axioms BinaryFormMoat.EntropyIntegration.normalized_eventWordHit_probability_le
#print axioms BinaryFormMoat.EntropyIntegration.sum_normalized_eventWordHit_probability_le
#print axioms BinaryFormMoat.EntropyIntegration.sum_weighted_normalized_eventWordHit_probability_le
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_event_shift_upper
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_error_budget
