import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction

namespace BinaryFormMoat

/-- Monic normalization preserves splitting: the normalized polynomial divides a
polynomial obtained simply by scaling all the roots. -/
theorem normalization_splits {K : Type*} [Field K] (f : Polynomial K) (hf : f ≠ 0)
    (hs : f.Splits) : f.integralNormalization.Splits := by
  apply (hs.scaleRoots f.leadingCoeff).of_dvd (Polynomial.scaleRoots_ne_zero hf _)
  rw [← Polynomial.integralNormalization_mul_C_leadingCoeff]
  exact dvd_mul_right _ _

/-- Scaling distinct roots preserves distinctness; this avoids a separate discriminant
calculation for the monic normalization. -/
theorem normalization_separable_of_splits {K : Type*} [Field K] (f : Polynomial K)
    (hsep : f.Separable) (hs : f.Splits) : f.integralNormalization.Separable := by
  have hf : f ≠ 0 := hsep.ne_zero
  have hl : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hn : (f.scaleRoots f.leadingCoeff).roots.Nodup := by
    rw [Polynomial.roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hl)]
    exact (Polynomial.nodup_roots hsep).map (mul_right_injective₀ hl)
  have hscale := (Polynomial.nodup_roots_iff_of_splits
    (Polynomial.scaleRoots_ne_zero hf _) (hs.scaleRoots f.leadingCoeff)).mp hn
  apply hscale.of_dvd
  rw [← Polynomial.integralNormalization_mul_C_leadingCoeff]
  exact dvd_mul_right _ _

/-- Rational separability survives integral monic normalization. -/
theorem normalization_separable {K : Type*} [Field K] (f : Polynomial K)
    (hsep : f.Separable) : f.integralNormalization.Separable := by
  let φ := algebraMap K f.SplittingField
  apply (Polynomial.separable_map φ).mp
  rw [← Polynomial.integralNormalization_map φ f
    (by simpa using φ.injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hsep.ne_zero))]
  exact normalization_separable_of_splits _ hsep.map (Polynomial.SplittingField.splits f)

/-- Monic normalization preserves the number of distinct roots over any field. -/
theorem normalization_card_roots {K : Type*} [Field K] [DecidableEq K]
    (f : Polynomial K) (hf : f ≠ 0) :
    f.integralNormalization.roots.toFinset.card = f.roots.toFinset.card := by
  classical
  have hl : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have he : f.integralNormalization.roots = f.roots.map (f.leadingCoeff * ·) := by
    rw [← Polynomial.roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hl),
      ← Polynomial.integralNormalization_mul_C_leadingCoeff,
      Polynomial.roots_mul (mul_ne_zero (Polynomial.monic_integralNormalization hf).ne_zero
        (Polynomial.C_ne_zero.mpr hl)), Polynomial.roots_C, add_zero]
  rw [he, Multiset.toFinset_map, Finset.card_image_of_injective _ (mul_right_injective₀ hl)]

/-- Monic normalization preserves roots after multiplication by the leading coefficient.
The residue map need not be injective: only the leading coefficient must remain nonzero. -/
theorem normalized_root_iff {K : Type*} [Field K] (f : Polynomial ℤ)
    (hdeg : 1 ≤ f.natDegree) (happ : ℤ →+* K) (ha : happ f.leadingCoeff ≠ 0) (x : K) :
    f.integralNormalization.eval₂ happ (happ f.leadingCoeff * x) = 0 ↔
      f.eval₂ happ x = 0 := by
  rw [Polynomial.integralNormalization_eval₂_leadingCoeff_mul hdeg happ x]
  simp only [mul_eq_zero, pow_ne_zero _ ha, false_or]

/-- This root-set equivalence lets monic root-reduction theorems handle arbitrary forms
after excluding primes dividing the leading coefficient. -/
noncomputable def normalizedRootEquiv {K : Type*} [Field K] (f : Polynomial ℤ)
    (hdeg : 1 ≤ f.natDegree) (happ : ℤ →+* K) (ha : happ f.leadingCoeff ≠ 0) :
    {x : K // f.eval₂ happ x = 0} ≃
      {y : K // f.integralNormalization.eval₂ happ y = 0} where
  toFun x := ⟨happ f.leadingCoeff * x.val,
    (normalized_root_iff f hdeg happ ha x.val).mpr x.property⟩
  invFun y := ⟨(happ f.leadingCoeff)⁻¹ * y.val, by
    apply (normalized_root_iff f hdeg happ ha _).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ ha, one_mul] using y.property⟩
  left_inv x := by
    apply Subtype.ext
    change (happ f.leadingCoeff)⁻¹ * (happ f.leadingCoeff * x.val) = x.val
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  right_inv y := by
    apply Subtype.ext
    change happ f.leadingCoeff * ((happ f.leadingCoeff)⁻¹ * y.val) = y.val
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

end BinaryFormMoat
