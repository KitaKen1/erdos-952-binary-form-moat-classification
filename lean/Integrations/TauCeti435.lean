import Moat.PrimeSupply
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.SplitsCompletely
import TauCeti.NumberTheory.NumberField.RootReduction

/-! Isolated integration probe, Lean 4.35.0-rc3 / TauCeti d5a3709.
This is not imported by the Lean 4.34.1 core. Check with scripts/check_tauceti.py.
RationalPrimes435 and PolynomialRoots435 transport these prime ideals to rational primes
and distinct polynomial roots, completing the arithmetic supply input of the moat proof. -/

namespace BinaryFormMoat.TauCetiIntegration
open Filter
open scoped Topology NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Specialize the proved Chebotarev asymptotic to the identity Frobenius class. -/
theorem completely_split_count_asymptotic :
    Tendsto (fun x : ℝ =>
      (NumberField.Chebotarev.frobeniusPrimeCount K L 1 x : ℝ) / (x / Real.log x))
      atTop (𝓝 (1 / (Module.finrank K L : ℝ))) := by
  simpa only [ConjClasses.one_eq_mk_one, Nat.card_coe_set_eq,
    ConjClasses.ncard_carrier_mk_of_mem_center (Subgroup.one_mem _), Nat.cast_one,
    IsGalois.card_aut_eq_finrank] using NumberField.Chebotarev.tendsto_frobeniusPrimeCount K L 1

/-- The imported, proved Chebotarev theorem supplies arbitrarily large completely split
prime-ideal quotas in every sufficiently distant doubling interval, after finite exclusions. -/
theorem eventually_completely_split_quota (B N : ℝ) :
    ∀ᶠ x : ℝ in atTop, N ≤
      (NumberField.Chebotarev.frobeniusPrimeCount K L 1 (2 * x) : ℝ) -
        (NumberField.Chebotarev.frobeniusPrimeCount K L 1 x : ℝ) - B := by
  exact eventually_dyadic_quota _ _ B N
    (one_div_pos.mpr (by exact_mod_cast Module.finrank_pos (R := K) (M := L)))
    (completely_split_count_asymptotic K L)

/-- Produce an actual finite batch of identity-Frobenius primes, avoiding a given finite set. -/
theorem eventually_completely_split_batch
    (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      T.card = N ∧ Disjoint T bad ∧
      ∀ v ∈ T, v ∈ NumberField.Chebotarev.frobeniusPrimeSet K L 1 ∧
        x < (Ideal.absNorm v.asIdeal : ℝ) ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ 2 * x := by
  classical
  let S (x : ℝ) := (TauCeti.primesLE K x).filter
    (· ∈ NumberField.Chebotarev.frobeniusPrimeSet K L 1)
  have hS : Tendsto (fun x : ℝ => (S x).card / (x / Real.log x))
      atTop (𝓝 (1 / (Module.finrank K L : ℝ))) := completely_split_count_asymptotic K L
  filter_upwards [eventually_exists_dyadic_batch S _
    (one_div_pos.mpr (by exact_mod_cast Module.finrank_pos (R := K) (M := L)))
    hS bad N] with x hx
  obtain ⟨T, hT, hbad, hcard⟩ := hx
  refine ⟨T, hcard, hbad, ?_⟩
  intro v hv
  have h := hT hv
  simp only [Finset.mem_sdiff, S, Finset.mem_filter, TauCeti.mem_normLE] at h
  exact ⟨h.1.2, lt_of_not_ge (fun hn => h.2 ⟨hn, h.1.2⟩), h.1.1⟩

/-- The available supply grows proportionally to x/log x, even after a finite exclusion.
This stronger form supports schedules whose batch sizes grow with the interval. -/
theorem eventually_completely_split_supply
    (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ((1 / (Module.finrank K L : ℝ)) / 2) * (x / Real.log x) ≤ (T.card : ℝ) ∧
      Disjoint T bad ∧
      ∀ v ∈ T, v ∈ NumberField.Chebotarev.frobeniusPrimeSet K L 1 ∧
        x < (Ideal.absNorm v.asIdeal : ℝ) ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ 2 * x := by
  classical
  let S (x : ℝ) := (TauCeti.primesLE K x).filter
    (· ∈ NumberField.Chebotarev.frobeniusPrimeSet K L 1)
  have hS : Tendsto (fun x : ℝ => (S x).card / (x / Real.log x))
      atTop (𝓝 (1 / (Module.finrank K L : ℝ))) := completely_split_count_asymptotic K L
  filter_upwards [eventually_dyadic_card_lower_bound S _
    (one_div_pos.mpr (by exact_mod_cast Module.finrank_pos (R := K) (M := L)))
    hS bad] with x hx
  refine ⟨(S (2 * x) \ S x) \ bad, hx, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (fun _ hv hb => (Finset.mem_sdiff.mp hv).2 hb)
  · intro v hv
    have h := (Finset.mem_sdiff.mp hv).1
    simp only [Finset.mem_sdiff, S, Finset.mem_filter, TauCeti.mem_normLE] at h
    exact ⟨h.1.2, lt_of_not_ge (fun hn => h.2 ⟨hn, h.1.2⟩), h.1.1⟩

end BinaryFormMoat.TauCetiIntegration

#print axioms NumberField.Chebotarev.tendsto_frobeniusPrimeCount
#print axioms NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet_one
#print axioms TauCeti.NumberField.splits_and_exists_rootSet_equiv_of_squarefree_map_zmod
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_completely_split_quota
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_completely_split_batch
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_completely_split_supply
