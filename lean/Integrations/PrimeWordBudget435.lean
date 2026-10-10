import Integrations.RootResidues435
import Integrations.ShortWordHits435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory
open scoped Classical

/-- Multiple root labels, including two coordinate slopes, form one event
per rational prime. -/
def rootPrimeHit (p : ℕ) (Q : (p : ℕ) → Finset (ZMod p)) (z : Point) : Prop :=
  ∃ ρ ∈ Q p, rootResidueHom p ρ z = 0

theorem rootPrimeHit_dvd_value (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (p : ℕ) (Q : (p : ℕ) → Finset (ZMod p))
    (hQ : ∀ ρ ∈ Q p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hz : rootPrimeHit p Q z) :
    p ∣ (value (f.homogenize n) z).natAbs := by
  obtain ⟨ρ, hρ, hh⟩ := hz
  exact rootResidueHom_zero_dvd_value f n hn p ρ (hQ ρ hρ) z hh

theorem rootPrimeHit_count_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (p : ℕ) → Finset (ZMod p))
    (hQ : ∀ p ∈ P, ∀ ρ ∈ Q p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hz : value (f.homogenize n) z ≠ 0) :
    (P.filter (fun p => rootPrimeHit p Q z)).card ≤ omega (value (f.homogenize n) z) := by
  apply le_trans (Finset.card_le_card ?_) (selected_prime_count_le P _ hz hP)
  intro p hp
  obtain ⟨hp, hh⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, rootPrimeHit_dvd_value f n hn p Q (hQ p hp) z hh⟩

/-- A union across a word charges at most the sum of its per-position
budgets. Repeated hits of a prime and repeated positions cause no problem. -/
theorem filter_exists_card_le_sum {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (P : Finset ι) (hit : ι → κ → Prop) :
    (P.filter (fun p => ∃ i, hit p i)).card ≤ ∑ i : κ, (P.filter (fun p => hit p i)).card := by
  have he : P.filter (fun p => ∃ i, hit p i) =
      Finset.univ.biUnion (fun i : κ => P.filter (fun p => hit p i)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, i, hi⟩
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp, hi⟩
      exact ⟨hp, i, hi⟩
  rw [he]
  exact Finset.card_biUnion_le

theorem rootPrimeWordHit_count_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (p : ℕ) → Finset (ZMod p))
    (hQ : ∀ p ∈ P, ∀ ρ ∈ Q p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (t L r : ℕ)
    (hz : ∀ i : Fin L, value (f.homogenize n) (z (t + i)) ≠ 0)
    (hr : ∀ i : Fin L, omega (value (f.homogenize n) (z (t + i))) ≤ r) :
    (P.filter (fun p => ∃ i : Fin L, rootPrimeHit p Q (z (t + i)))).card ≤ L * r := by
  have h := filter_exists_card_le_sum (κ := Fin L) P
    (fun p i => rootPrimeHit p Q (z (t + i)))
  have hs : (∑ i : Fin L, (P.filter (fun p => rootPrimeHit p Q (z (t + i)))).card) ≤
      ∑ _i : Fin L, r := Finset.sum_le_sum (fun i _ =>
    (rootPrimeHit_count_le f n hn P hP Q hQ _ (hz i)).trans (hr i))
  convert h.trans (by simpa using hs) using 1
  congr 1
  ext p
  simp

section CountableSource
variable {Ω ι : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_filter_card (P : Finset ι) (hit : ι → Ω → Prop) :
    (∫ ω, ((P.filter (fun p => hit p ω)).card : ℝ) ∂μ) =
      ∑ p ∈ P, μ.real {ω | hit p ω} := by
  have he (ω : Ω) : ((P.filter (fun p => hit p ω)).card : ℝ) =
      ∑ p ∈ P, if hit p ω then 1 else 0 := by simp
  have hi (p : ι) : Integrable (fun ω => if hit p ω then (1 : ℝ) else 0) μ := by
    have hf : (fun ω => if hit p ω then (1 : ℝ) else 0) =
        {ω | hit p ω}.indicator 1 := by ext ω; simp [Set.indicator_apply]
    rw [hf]
    exact (integrable_const _).indicator (Set.to_countable _).measurableSet
  simp_rw [he]
  rw [integral_finsetSum _ (fun p _ => hi p)]
  apply Finset.sum_congr rfl
  intro p _
  have hf : (fun ω => if hit p ω then (1 : ℝ) else 0) =
      {ω | hit p ω}.indicator 1 := by ext ω; simp [Set.indicator_apply]
  rw [hf, integral_indicator_one (Set.to_countable _).measurableSet]

/-- Average the pointwise distinct-prime budget under the actual law. -/
theorem sum_hit_probability_le_of_count (P : Finset ι) (hit : ι → Ω → Prop) (r : ℕ)
    (hr : ∀ ω, (P.filter (fun p => hit p ω)).card ≤ r) :
    ∑ p ∈ P, μ.real {ω | hit p ω} ≤ r := by
  rw [← integral_filter_card μ P hit]
  have hi : Integrable (fun ω => ((P.filter (fun p => hit p ω)).card : ℝ)) μ := by
    apply Integrable.mono' (integrable_const (P.card : ℝ))
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with ω
    simpa using (show ((P.filter (fun p => hit p ω)).card : ℝ) ≤ P.card by
      exact_mod_cast Finset.card_filter_le P (fun p => hit p ω))
  calc
    _ ≤ ∫ _ω, (r : ℝ) ∂μ := integral_mono hi (integrable_const _) (fun ω => by
      exact Nat.cast_le.mpr (hr ω))
    _ = _ := by simp

end CountableSource

/-- No independence, uniform-time law, primitivity or self-avoidance is
needed for this upper error budget. -/
theorem sum_rootPrimeWordHit_probability_le {Ω : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (p : ℕ) → Finset (ZMod p))
    (hQ : ∀ p ∈ P, ∀ ρ ∈ Q p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (a : Ω → ℕ) (L r : ℕ)
    (hz : ∀ ω (i : Fin L), value (f.homogenize n) (z (a ω + i)) ≠ 0)
    (hr : ∀ ω (i : Fin L), omega (value (f.homogenize n) (z (a ω + i))) ≤ r) :
    ∑ p ∈ P, μ.real {ω | ∃ i : Fin L, rootPrimeHit p Q (z (a ω + i))} ≤ (L * r : ℕ) := by
  exact sum_hit_probability_le_of_count μ P
    (fun p ω => ∃ i : Fin L, rootPrimeHit p Q (z (a ω + i))) (L * r)
    (fun ω => by
      have h := rootPrimeWordHit_count_le f n hn P hP Q hQ z (a ω) L r (hz ω) (hr ω)
      convert h using 1
      congr 1
      ext p
      simp)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.rootPrimeHit_dvd_value
#print axioms BinaryFormMoat.EntropyIntegration.rootPrimeHit_count_le
#print axioms BinaryFormMoat.EntropyIntegration.filter_exists_card_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.rootPrimeWordHit_count_le
#print axioms BinaryFormMoat.EntropyIntegration.integral_filter_card
#print axioms BinaryFormMoat.EntropyIntegration.sum_hit_probability_le_of_count
#print axioms BinaryFormMoat.EntropyIntegration.sum_rootPrimeWordHit_probability_le
