import Integrations.TauCeti435

namespace BinaryFormMoat.TauCetiIntegration
open Filter IsDedekindDomain
open scoped Topology NumberField

/-- The natural generator identifies the underlying integer prime ideal. -/
theorem rational_prime_under (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.under ℤ = Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)} := by
  ext n
  change (algebraMap ℤ (𝓞 ℚ) n ∈ v.asIdeal) ↔ n ∈ Ideal.span {_}
  rw [Ideal.mem_span_singleton, Int.natCast_dvd]
  cases n with
  | ofNat n =>
    change (algebraMap ℤ (𝓞 ℚ) (n : ℤ) ∈ v.asIdeal) ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n
    simpa only [map_natCast, Int.natAbs_natCast, Rat.HeightOneSpectrum.absNorm_asIdeal] using
      (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd v (n := n))
  | negSucc n =>
    change (algebraMap ℤ (𝓞 ℚ) (-((n + 1 : ℕ) : ℤ)) ∈ v.asIdeal) ↔ _
    simpa only [map_neg, map_natCast, Int.natAbs_negSucc,
      Ideal.neg_mem_iff, Rat.HeightOneSpectrum.absNorm_asIdeal] using
      (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd v (n := n + 1))

/-- Identity Frobenius over the ring of integers of Q gives complete splitting over Z. -/
theorem rational_prime_splits (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ L 1) :
    ((Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)}).primesOver (𝓞 L)).ncard =
      Module.finrank ℚ L := by
  have hs := NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank.mp hv
  have he := Ideal.primesOver_under_ringOfIntegers_rat_eq (S := 𝓞 L) v.asIdeal
    (p := v.asIdeal.under ℤ)
  have hunder : v.asIdeal.under (𝓞 ℚ) = v.asIdeal := by simp [Ideal.under_def]
  rw [hunder, rational_prime_under] at he
  rwa [← he]

/-- Chebotarev supplies actual rational primes in each sufficiently distant doubling interval,
with arbitrary finite exclusions and exactly the prescribed number of distinct primes. -/
theorem eventually_rational_split_batch (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (bad : Finset ℕ) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ, T.card = N ∧ Disjoint T bad ∧
      ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L := by
  classical
  filter_upwards [eventually_completely_split_batch ℚ L ∅ N,
    eventually_gt_atTop ((bad.sup id : ℕ) : ℝ)] with x hx hxb
  obtain ⟨S, hcard, _, hS⟩ := hx
  let g := Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)
  have hinj : Function.Injective g := by
    intro v w h
    apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    exact Subtype.ext h
  refine ⟨S.image g, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hcard]
  · apply Finset.disjoint_left.mpr
    intro p hp hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    have hlow := (hS v hv).2.1
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hlow
    have hb' : g v ≤ bad.sup id := Finset.le_sup (f := id) hb
    have hb'' : (g v : ℝ) ≤ ((bad.sup id : ℕ) : ℝ) := by exact_mod_cast hb'
    exact (not_lt_of_ge (hb''.trans hxb.le)) hlow
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmem, hlo, hhi⟩ := hS v hv
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hlo hhi
    exact ⟨Rat.HeightOneSpectrum.prime_natGenerator v, hlo, hhi,
      rational_prime_splits L v hmem⟩

/-- A quantitative rational-prime supply, with density constant depending only on the field. -/
theorem eventually_rational_split_supply (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (bad : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ,
      ((1 / (Module.finrank ℚ L : ℝ)) / 2) * (x / Real.log x) ≤ (T.card : ℝ) ∧
      Disjoint T bad ∧ ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L := by
  classical
  filter_upwards [eventually_completely_split_supply ℚ L ∅,
    eventually_gt_atTop ((bad.sup id : ℕ) : ℝ)] with x hx hxb
  obtain ⟨S, hcard, _, hS⟩ := hx
  let g := Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)
  have hinj : Function.Injective g := by
    intro v w h
    apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    exact Subtype.ext h
  refine ⟨S.image g, ?_, ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ hinj]
  · apply Finset.disjoint_left.mpr
    intro p hp hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    have hlow := (hS v hv).2.1
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hlow
    have hb' : g v ≤ bad.sup id := Finset.le_sup (f := id) hb
    have hb'' : (g v : ℝ) ≤ ((bad.sup id : ℕ) : ℝ) := by exact_mod_cast hb'
    exact (not_lt_of_ge (hb''.trans hxb.le)) hlow
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmem, hlo, hhi⟩ := hS v hv
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hlo hhi
    exact ⟨Rat.HeightOneSpectrum.prime_natGenerator v, hlo, hhi,
      rational_prime_splits L v hmem⟩

end BinaryFormMoat.TauCetiIntegration

#print axioms BinaryFormMoat.TauCetiIntegration.rational_prime_under
#print axioms BinaryFormMoat.TauCetiIntegration.rational_prime_splits
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_rational_split_batch
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_rational_split_supply
