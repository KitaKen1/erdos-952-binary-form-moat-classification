import Integrations.PolynomialRoots435
import Integrations.RectangleHarper435
import Moat.RectangleExistence

namespace BinaryFormMoat.TauHarperIntegration
open Filter
open scoped Topology

/-- Quantitative arithmetic supply on integer dyadic scales, with an arbitrary
quota selected after the scale. The constant precedes every finite exclusion. -/
theorem exists_irreducible_nat_root_quota (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ T : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ c * ((T : ℝ) / Real.log T) →
        ∃ P : Finset ℕ, P.card = N ∧ Disjoint P bad ∧
          ∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ rootCountMod f p = f.natDegree := by
  classical
  obtain ⟨c, hc, hsupply⟩ := TauCetiIntegration.exists_irreducible_root_supply f hf hd
  refine ⟨c, hc, fun bad => ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop :
    Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop).eventually (hsupply bad)] with T hT
  obtain ⟨Q, hQcard, hQbad, hQ⟩ := hT
  intro N hN
  have hNQ : N ≤ Q.card := by exact_mod_cast hN.trans hQcard
  obtain ⟨P, hPQ, hPcard⟩ := Finset.exists_subset_card_eq hNQ
  refine ⟨P, hPcard, hQbad.mono_left hPQ, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hhi, hroots⟩ := hQ p (hPQ hp)
  refine ⟨hprime, ?_, ?_, hroots⟩
  · exact le_of_lt (by exact_mod_cast hlo)
  · exact_mod_cast hhi

/-- Flexible local parameters for approaching the prime-product area threshold.
The batch precedes eta and both rectangle dimensions. All scalar budgets remain
visible, rather than specializing to the coarse q=12 window. -/
theorem exists_rectangle_batch_with_parameters (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ T : ℕ in atTop, ∀ q l : ℕ, 2 ≤ q → 1 ≤ l →
        ((2 * q * l : ℕ) : ℝ) ≤ c * ((T : ℝ) / Real.log T) →
        ∃ P : Finset ℕ, P.card = 2 * q * l ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
            (primeRootSet f p).card = f.natDegree) ∧
          ∀ (η : ℝ) (A B : ℕ), 0 ≤ η → 3 ≤ (η ^ 2 / 2) * q →
            Real.log ((max A B : ℕ) : ℝ) +
              Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
              (1 - η) * (2 * q * l : ℕ) * Real.log (T : ℝ) →
            2 * A * B < T ^ ((2 * q - 4) * l) →
            ((rectangleWitnessEvent P (primeRootSet f) A B).card : ℝ) /
                Fintype.card (∀ p : P, primeRootSet f p) ≤
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
  refine ⟨P, hcard, hbad, fun p hp => ?_, fun η A B hη hschedule hsize harea => ?_⟩
  · exact ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1, hroots p hp⟩
  · apply HarperIntegration.harper_rectangle_exp_tail_of_dyadic_bounds f hf hd P
      (fun p hp => (hP p hp).1) (primeRootSet f) hroots
      (fun p hp ρ hρ => (mem_primeRootSet f p (hP p hp).1 ρ).mp hρ)
      q l hq hl hcard A B T hT (fun p hp => (hP p hp).2.1)
      (fun p hp => (hP p hp).2.2.1) η hη hschedule _ harea
    simpa only [hcard] using hsize

/-- Tau Ceti supplies the primes and the canonical root alphabets; Harper
supplies the all-line bound. The batch is chosen before the rectangle dimensions.
The length may vary with the scale, subject only to the quantitative prime quota. -/
theorem exists_rectangle_batch_of_quota (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ T : ℕ in atTop, ∀ l : ℕ, 1 ≤ l →
        (24 * l : ℝ) ≤ c * ((T : ℝ) / Real.log T) →
        ∃ P : Finset ℕ, P.card = 24 * l ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
            (primeRootSet f p).card = f.natDegree) ∧
          ∀ A B : ℕ, Real.log ((max A B : ℕ) : ℝ) +
              Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
              6 * l * Real.log (T : ℝ) →
            ((rectangleWitnessEvent P (primeRootSet f) A B).card : ℝ) /
                Fintype.card (∀ p : P, primeRootSet f p) ≤
              Real.exp (-(l : ℝ) / (48 * ((2304 * f.natDegree + 4 : ℕ) : ℝ))) := by
  obtain ⟨c, hc, hquota⟩ := exists_irreducible_nat_root_quota f hf hd
  refine ⟨c, hc, fun bad => ?_⟩
  filter_upwards [hquota bad, eventually_ge_atTop 2] with T hquotaT hT
  intro l hl hcapacity
  obtain ⟨P, hcard, hbad, hP⟩ := hquotaT (24 * l) (by simpa using hcapacity)
  have hroots : ∀ p ∈ P, (primeRootSet f p).card = f.natDegree := by
    intro p hp
    rw [card_primeRootSet f p (hP p hp).1, (hP p hp).2.2.2]
  refine ⟨P, hcard, hbad, fun p hp => ?_, fun A B hsize => ?_⟩
  · exact ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1, hroots p hp⟩
  · exact HarperIntegration.harper_rectangle_exp_tail_concrete f hf hd P
      (fun p hp => (hP p hp).1) (primeRootSet f) hroots
      (fun p hp ρ hρ => (mem_primeRootSet f p (hP p hp).1 ρ).mp hρ)
      l hl hcard A B T hT (fun p hp => (hP p hp).2.1)
      (fun p hp => (hP p hp).2.2.1) hsize

/-- A coarse radius window reserves one unit of logarithmic budget for the
coefficient cost. The zero-radius case uses Lean's convention log(0)=0. -/
theorem rectangle_size_budget_of_power_bound (f : Polynomial ℤ) (l A B T : ℕ)
    (hl : 1 ≤ l) (hT : 2 ≤ T) (hR : max A B ≤ T ^ (5 * l))
    (hC : Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      Real.log (T : ℝ)) :
    Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      6 * l * Real.log (T : ℝ) := by
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have hlogR : Real.log ((max A B : ℕ) : ℝ) ≤ 5 * l * Real.log (T : ℝ) := by
    by_cases hzero : max A B = 0
    · rw [hzero, Nat.cast_zero, Real.log_zero]
      positivity
    · have hpos : (0 : ℝ) < (max A B : ℕ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hzero)
      have h := Real.log_le_log hpos (show ((max A B : ℕ) : ℝ) ≤ (T ^ (5 * l) : ℕ) by
        exact_mod_cast hR)
      rw [Nat.cast_pow, Real.log_pow] at h
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

/-- All sufficiently large scales admit every length allowed by prime supply.
Each batch works uniformly for the whole radius window max(A,B)<=T^(5*l). -/
theorem exists_rectangle_window_batch (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ T : ℕ in atTop, ∀ l : ℕ, 1 ≤ l →
        (24 * l : ℝ) ≤ c * ((T : ℝ) / Real.log T) →
        ∃ P : Finset ℕ, P.card = 24 * l ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
            (primeRootSet f p).card = f.natDegree) ∧
          ∀ A B : ℕ, max A B ≤ T ^ (5 * l) →
            ((rectangleWitnessEvent P (primeRootSet f) A B).card : ℝ) /
                Fintype.card (∀ p : P, primeRootSet f p) ≤
              Real.exp (-(l : ℝ) / (48 * ((2304 * f.natDegree + 4 : ℕ) : ℝ))) := by
  obtain ⟨c, hc, hbatch⟩ := exists_rectangle_batch_of_quota f hf hd
  refine ⟨c, hc, fun bad => ?_⟩
  have hcoef : ∀ᶠ T : ℕ in atTop,
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤ Real.log (T : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [hbatch bad, hcoef, eventually_ge_atTop 2] with T hbatchT hC hT
  intro l hl hcapacity
  obtain ⟨P, hcard, hbad, hP, hrect⟩ := hbatchT l hl hcapacity
  exact ⟨P, hcard, hbad, hP, fun A B hR =>
    hrect A B (rectangle_size_budget_of_power_bound f l A B T hl hT hR hC)⟩

/-- Any fixed positive length fits the prime quota eventually; no arithmetic
or rectangle condition remains beyond membership in the radius window. -/
theorem eventually_rectangle_window_batch (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (bad : Finset ℕ) (l : ℕ) (hl : 1 ≤ l) :
    ∀ᶠ T : ℕ in atTop, ∃ P : Finset ℕ, P.card = 24 * l ∧ Disjoint P bad ∧
      (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
        (primeRootSet f p).card = f.natDegree) ∧
      ∀ A B : ℕ, max A B ≤ T ^ (5 * l) →
        ((rectangleWitnessEvent P (primeRootSet f) A B).card : ℝ) /
            Fintype.card (∀ p : P, primeRootSet f p) ≤
          Real.exp (-(l : ℝ) / (48 * ((2304 * f.natDegree + 4 : ℕ) : ℝ))) := by
  obtain ⟨c, hc, hbatch⟩ := exists_rectangle_window_batch f hf hd
  have hcapacity : ∀ᶠ T : ℕ in atTop, (24 * l : ℝ) ≤ c * ((T : ℝ) / Real.log T) :=
    ((tendsto_primeCountingScale.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop)).const_mul_atTop
        hc).eventually (eventually_ge_atTop _)
  filter_upwards [hbatch bad, hcapacity] with T hbatchT hquota
  exact hbatchT l hl hquota

/-- A concrete local sieve exists throughout the radius window. All primes,
root alphabets and the one root assignment are constructed in the proof.
This excludes homogeneous slope witnesses, not arbitrary moat walks. -/
theorem eventually_exists_rectangle_avoiding_batch (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (bad : Finset ℕ) (l : ℕ) (hl : 1 ≤ l) :
    ∀ᶠ T : ℕ in atTop, ∃ P : Finset ℕ, P.card = 24 * l ∧ Disjoint P bad ∧
      (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧
        (primeRootSet f p).card = f.natDegree) ∧
      ∃ σ : (∀ p : P, primeRootSet f p), ∀ A B : ℕ, max A B ≤ T ^ (5 * l) →
        ∀ z ∈ rectanglePoints A B, z ≠ (0, 0) →
          ∃ p : P, (z.1 : ZMod p.val) ≠ (σ p).val * (z.2 : ZMod p.val) := by
  filter_upwards [eventually_rectangle_window_batch f hf hd bad l hl] with T hT
  obtain ⟨P, hcard, hbad, hP, hrect⟩ := hT
  have hS : ∀ p : P, (primeRootSet f p).Nonempty := by
    intro p
    apply Finset.card_pos.mp
    rw [(hP p p.property).2.2.2]
    omega
  have htail := hrect (T ^ (5 * l)) (T ^ (5 * l)) (by simp)
  have hexp : Real.exp (-(l : ℝ) / (48 * ((2304 * f.natDegree + 4 : ℕ) : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    apply div_neg_of_neg_of_pos
    · have : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      linarith
    · positivity
  obtain ⟨σ, hσ⟩ := exists_rectangle_avoiding_root_assignment P (primeRootSet f) hS
    (T ^ (5 * l)) (T ^ (5 * l)) (htail.trans_lt hexp)
  refine ⟨P, hcard, hbad, hP, σ, fun A B hR z hz hzero => ?_⟩
  apply hσ z _ hzero
  rw [mem_rectanglePoints] at hz ⊢
  exact ⟨hz.1.trans ((le_max_left A B).trans hR),
    hz.2.trans ((le_max_right A B).trans hR)⟩

end BinaryFormMoat.TauHarperIntegration
