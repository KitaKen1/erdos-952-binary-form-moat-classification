import Integrations.RationalPrimes435
import Moat.GoodReduction
import Moat.Normalization
import Moat.RootCount
import Moat.ArithmeticInput

namespace BinaryFormMoat.TauCetiIntegration
open Polynomial Filter
open scoped Topology NumberField

/-- A completely split rational prime gives a reduction homomorphism to its prime field. -/
theorem exists_reduction_to_zmod (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [Fact p.Prime]
    (hsplit : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L) :
    Nonempty (𝓞 L →+* ZMod p) := by
  obtain ⟨Q, hQprime, hQover⟩ :=
    (Ideal.nonempty_primesOver (S := 𝓞 L) (Ideal.span {(p : ℤ)})).some
  let : Q.IsPrime := hQprime
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover
  let e := RingEquiv.ofBijective (algebraMap (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 L ⧸ Q))
    (Ideal.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank Q hsplit)
  exact ⟨(Int.quotientSpanNatEquivZMod p).toRingHom.comp
    (e.symm.toRingHom.comp (Ideal.Quotient.mk Q))⟩

/-- Monic polynomials that split in the number field have exactly degree-many distinct
roots modulo every completely split prime of good reduction. -/
theorem card_roots_mod_prime_of_splits (L : Type*) [Field L] [NumberField L]
    (f : Polynomial ℤ) (hf : f.Monic)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ L)).Splits)
    (p : ℕ) [Fact p.Prime]
    (hp : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L)
    (hsep : (f.map (Int.castRingHom (ZMod p))).Separable) :
    rootCountMod f p = f.natDegree := by
  classical
  obtain ⟨ρ⟩ := exists_reduction_to_zmod L p hp
  have hs := (TauCeti.NumberField.splits_and_exists_rootSet_equiv_of_squarefree_map_zmod
    (M := L) hf hsep.squarefree hsplit ρ).1
  have hs' : (f.map (Int.castRingHom (ZMod p))).Splits := by simpa using hs
  rw [rootCountMod_eq_roots f p (map_monic_ne_zero hf),
    Multiset.toFinset_card_of_nodup (nodup_roots hsep), ← hs'.natDegree_eq_card_roots]
  exact natDegree_map_eq_of_isUnit_leadingCoeff _ (by rw [hf.leadingCoeff]; exact isUnit_one)

/-- All sufficiently distant doubling intervals contain any prescribed finite number of
primes where a fixed monic separable polynomial has degree-many distinct roots. -/
theorem eventually_monic_root_batch (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (f : Polynomial ℤ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ L)).Splits)
    (bad : Finset ℕ) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ, T.card = N ∧ Disjoint T bad ∧
      ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        rootCountMod f p = f.natDegree := by
  classical
  obtain ⟨c, hc, hgood⟩ := exists_good_reduction_modulus f hdeg hsep
  filter_upwards [eventually_rational_split_batch L (bad ∪ c.natAbs.primeFactors) N]
    with x hx
  obtain ⟨T, hcard, hbad, hT⟩ := hx
  refine ⟨T, hcard, hbad.mono_right Finset.subset_union_left, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hhi, hsplitp⟩ := hT p hp
  let : Fact p.Prime := ⟨hprime⟩
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro h
    apply Finset.disjoint_left.mp hbad hp
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hprime, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hc⟩)
  exact ⟨hprime, hlo, hhi, card_roots_mod_prime_of_splits L f hf hsplit p hsplitp (hgood p hpc).2⟩

/-- Choosing a splitting field discharges all number-field hypotheses in the monic case. -/
theorem eventually_monic_root_batch_of_separable
    (f : Polynomial ℤ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) (bad : Finset ℕ) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ, T.card = N ∧ Disjoint T bad ∧
      ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        rootCountMod f p = f.natDegree := by
  let L := (f.map (Int.castRingHom ℚ)).SplittingField
  let : NumberField L := NumberField.of_module_finite ℚ L
  let : IsGalois ℚ L := IsGalois.of_separable_splitting_field hsep
  exact eventually_monic_root_batch L f hf hdeg hsep
    (Polynomial.SplittingField.splits _) bad N

/-- Positive-degree integer polynomials separable over Q have arbitrarily large finite
batches of rational primes, in each sufficiently distant doubling interval, with degree-many
distinct roots. Nonmonic polynomials are handled by integral normalization. -/
theorem eventually_polynomial_root_batch
    (f : Polynomial ℤ) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) (bad : Finset ℕ) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ, T.card = N ∧ Disjoint T bad ∧
      ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        rootCountMod f p = f.natDegree := by
  classical
  have hf : f ≠ 0 := by intro h; simp [h] at hdeg
  have hl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hlq : (Int.castRingHom ℚ) f.leadingCoeff ≠ 0 := by simpa using hl
  have hgn : f.integralNormalization.natDegree = f.natDegree := natDegree_integralNormalization
  have hgsep : (f.integralNormalization.map (Int.castRingHom ℚ)).Separable := by
    rw [← integralNormalization_map _ _ hlq]
    exact normalization_separable _ hsep
  filter_upwards [eventually_monic_root_batch_of_separable f.integralNormalization
    (monic_integralNormalization hf) (by omega) hgsep
    (bad ∪ f.leadingCoeff.natAbs.primeFactors) N] with x hx
  obtain ⟨T, hcard, hbad, hT⟩ := hx
  refine ⟨T, hcard, hbad.mono_right Finset.subset_union_left, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hhi, hroots⟩ := hT p hp
  let : Fact p.Prime := ⟨hprime⟩
  have hlp : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    change (f.leadingCoeff : ZMod p) ≠ 0
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    apply Finset.disjoint_left.mp hbad hp
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hprime, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hl⟩)
  rw [← rootCountMod_normalization f (by omega) p hlp, hgn] at hroots
  exact ⟨hprime, hlo, hhi, hroots⟩

/-- Quantitative supply for a monic polynomial split in a fixed Galois number field. -/
theorem eventually_monic_root_supply (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (f : Polynomial ℤ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ L)).Splits) (bad : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ,
      ((1 / (Module.finrank ℚ L : ℝ)) / 2) * (x / Real.log x) ≤ (T.card : ℝ) ∧
      Disjoint T bad ∧ ∀ p ∈ T,
        p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ rootCountMod f p = f.natDegree := by
  classical
  obtain ⟨c, hc, hgood⟩ := exists_good_reduction_modulus f hdeg hsep
  filter_upwards [eventually_rational_split_supply L (bad ∪ c.natAbs.primeFactors)] with x hx
  obtain ⟨T, hcard, hbad, hT⟩ := hx
  refine ⟨T, hcard, hbad.mono_right Finset.subset_union_left, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hhi, hsplitp⟩ := hT p hp
  let : Fact p.Prime := ⟨hprime⟩
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro h
    apply Finset.disjoint_left.mp hbad hp
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hprime, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hc⟩)
  exact ⟨hprime, hlo, hhi, card_roots_mod_prime_of_splits L f hf hsplit p hsplitp (hgood p hpc).2⟩

/-- The arithmetic input in the needed quantitative form: a positive constant depending
only on f supplies at least c*x/log(x) rational primes with degree-many distinct roots.
The constant is chosen before the arbitrary finite exceptional set. -/
theorem exists_polynomial_root_supply
    (f : Polynomial ℤ) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ,
        c * (x / Real.log x) ≤ (T.card : ℝ) ∧ Disjoint T bad ∧
        ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
          rootCountMod f p = f.natDegree := by
  classical
  have hf : f ≠ 0 := by intro h; simp [h] at hdeg
  have hl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hlq : (Int.castRingHom ℚ) f.leadingCoeff ≠ 0 := by simpa using hl
  have hgn : f.integralNormalization.natDegree = f.natDegree := natDegree_integralNormalization
  have hgsep : (f.integralNormalization.map (Int.castRingHom ℚ)).Separable := by
    rw [← integralNormalization_map _ _ hlq]
    exact normalization_separable _ hsep
  let L := (f.integralNormalization.map (Int.castRingHom ℚ)).SplittingField
  let : NumberField L := NumberField.of_module_finite ℚ L
  let : IsGalois ℚ L := IsGalois.of_separable_splitting_field hgsep
  refine ⟨(1 / (Module.finrank ℚ L : ℝ)) / 2, ?_, ?_⟩
  · exact div_pos (one_div_pos.mpr (by exact_mod_cast Module.finrank_pos (R := ℚ) (M := L)))
      (by norm_num)
  intro bad
  filter_upwards [eventually_monic_root_supply L f.integralNormalization
    (monic_integralNormalization hf) (by omega) hgsep (Polynomial.SplittingField.splits _)
    (bad ∪ f.leadingCoeff.natAbs.primeFactors)] with x hx
  obtain ⟨T, hcard, hbad, hT⟩ := hx
  refine ⟨T, hcard, hbad.mono_right Finset.subset_union_left, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hhi, hroots⟩ := hT p hp
  let : Fact p.Prime := ⟨hprime⟩
  have hlp : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    change (f.leadingCoeff : ZMod p) ≠ 0
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    apply Finset.disjoint_left.mp hbad hp
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hprime, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hl⟩)
  rw [← rootCountMod_normalization f (by omega) p hlp, hgn] at hroots
  exact ⟨hprime, hlo, hhi, hroots⟩

/-- The exact high-degree irreducible input of the moat classification has quantitative
prime supply; no number field or separability assumption remains to be discharged. -/
theorem exists_irreducible_root_supply (f : Polynomial ℤ) (hf : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ,
      ∀ᶠ x : ℝ in atTop, ∃ T : Finset ℕ,
        c * (x / Real.log x) ≤ (T.card : ℝ) ∧ Disjoint T bad ∧
        ∀ p ∈ T, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
          rootCountMod f p = f.natDegree :=
  exists_polynomial_root_supply f (by omega) (irreducible_rat_map_separable f hf hdeg)

end BinaryFormMoat.TauCetiIntegration

#print axioms BinaryFormMoat.TauCetiIntegration.exists_reduction_to_zmod
#print axioms BinaryFormMoat.TauCetiIntegration.card_roots_mod_prime_of_splits
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_monic_root_batch
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_monic_root_batch_of_separable
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_polynomial_root_batch
#print axioms BinaryFormMoat.TauCetiIntegration.eventually_monic_root_supply
#print axioms BinaryFormMoat.TauCetiIntegration.exists_polynomial_root_supply
#print axioms BinaryFormMoat.TauCetiIntegration.exists_irreducible_root_supply
