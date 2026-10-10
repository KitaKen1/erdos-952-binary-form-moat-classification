import Integrations.TauHarper435
import Integrations.FiniteSetHarper435

namespace BinaryFormMoat.TauHarperIntegration
open Filter
open scoped Topology

/-- The prime batch is chosen before orientation, dimensions and tail parameters.
This is a uniform probability bound for individual rotated rectangles. -/
theorem exists_rotated_rectangle_batch_with_parameters
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ T : ℕ in atTop, ∀ q l : ℕ, 2 ≤ q → 1 ≤ l →
        ((2 * q * l : ℕ) : ℝ) ≤ c * ((T : ℝ) / Real.log T) →
        ∃ P : Finset ℕ, P.card = 2 * q * l ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
            (primeRootSet f p).card = f.natDegree) ∧
          ∀ (a b η : ℝ) (A B : ℕ), a ^ 2 + b ^ 2 = 1 →
            0 ≤ η → 3 ≤ (η ^ 2 / 2) * q →
            Real.log ((A + B : ℕ) : ℝ) +
              Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
              (1 - η) * (2 * q * l : ℕ) * Real.log (T : ℝ) →
            2 * A * B < T ^ ((2 * q - 4) * l) →
            ((finiteSetWitnessEvent (rotatedRectanglePoints a b A B) P
                (primeRootSet f)).card : ℝ) / Fintype.card (∀ p : P, primeRootSet f p) ≤
              Real.exp (-(l : ℝ) /
                (4 * (((16 * f.natDegree * q ^ 2 + 4) * q : ℕ) : ℝ))) := by
  obtain ⟨c, hc, hquota⟩ := exists_irreducible_nat_root_quota f hf hd
  refine ⟨c, hc, fun bad => ?_⟩
  filter_upwards [hquota bad, eventually_ge_atTop 2] with T hquotaT hT
  intro q l hq hl hcapacity
  obtain ⟨P, hcard, hbad, hP⟩ := hquotaT (2 * q * l) hcapacity
  have hroots : ∀ p ∈ P, (primeRootSet f p).card = f.natDegree := by
    intro p hp
    rw [card_primeRootSet f p (hP p hp).1, (hP p hp).2.2.2]
  refine ⟨P, hcard, hbad, fun p hp => ?_,
    fun a b η A B hab hη hschedule hsize harea => ?_⟩
  · exact ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1, hroots p hp⟩
  · apply HarperIntegration.harper_rotated_rectangle_exp_tail_of_dyadic_bounds f hf hd P
      (fun p hp => (hP p hp).1) (primeRootSet f) hroots
      (fun p hp ρ hρ => (mem_primeRootSet f p (hP p hp).1 ρ).mp hρ)
      q l hq hl hcard a b hab A B T hT (fun p hp => (hP p hp).2.1)
      (fun p hp => (hP p hp).2.2.1) η hη hschedule _ harea
    simpa only [hcard] using hsize

end BinaryFormMoat.TauHarperIntegration
