import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Field.ZMod

namespace BinaryFormMoat
open Polynomial

/-- Separability over the rationals admits an integer Bezout certificate with a nonzero
constant. Working with the resultant avoids clearing arbitrary rational denominators. -/
theorem exists_separability_certificate (f : Polynomial ℤ) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ (c : ℤ) (a b : Polynomial ℤ), c ≠ 0 ∧ f * a + f.derivative * b = C c := by
  let c := f.resultant f.derivative
  have hc : c ≠ 0 := by
    have h := resultant_ne_zero (f.map (Int.castRingHom ℚ))
      (f.derivative.map (Int.castRingHom ℚ)) (by simpa only [separable_def, derivative_map] using hsep)
    rw [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective (Int.castRingHom ℚ)),
      natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective (Int.castRingHom ℚ)),
      resultant_map_map] at h
    exact fun hz => h (by change (Int.castRingHom ℚ) c = 0; rw [hz, map_zero])
  obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl le_rfl (Or.inl (Nat.ne_of_gt hdeg))
  exact ⟨c, a, b, hc, hab⟩

/-- A Bezout certificate remains valid modulo every prime not dividing its constant. -/
theorem separable_mod_prime_of_certificate (f a b : Polynomial ℤ) (c : ℤ)
    (hab : f * a + f.derivative * b = C c) (p : ℕ) [Fact p.Prime]
    (hc : ¬ (p : ℤ) ∣ c) : (f.map (Int.castRingHom (ZMod p))).Separable := by
  have hc0 : (c : ZMod p) ≠ 0 := by
    simpa only [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] using hc
  let φ := Int.castRingHom (ZMod p)
  have he := congrArg (Polynomial.map φ) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at he
  change IsCoprime (f.map φ) (f.map φ).derivative
  refine ⟨C (c : ZMod p)⁻¹ * a.map φ, C (c : ZMod p)⁻¹ * b.map φ, ?_⟩
  calc
    _ = C (c : ZMod p)⁻¹ * (f.map φ * a.map φ + (f.map φ).derivative * b.map φ) := by ring
    _ = 1 := by rw [he, ← C_mul]; simp [φ, hc0]

/-- A single nonzero integer excludes every prime where degree or separability could fail. -/
theorem exists_good_reduction_modulus (f : Polynomial ℤ) (hdeg : 0 < f.natDegree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ N →
      (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree ∧
      (f.map (Int.castRingHom (ZMod p))).Separable := by
  obtain ⟨c, a, b, hc, hab⟩ := exists_separability_certificate f hdeg hsep
  have hf0 : f ≠ 0 := by intro h; simp [h] at hdeg
  refine ⟨c * f.leadingCoeff, mul_ne_zero hc (leadingCoeff_ne_zero.mpr hf0), ?_⟩
  intro p hp hN
  have hc' : ¬ (p : ℤ) ∣ c := fun h => hN (dvd_mul_of_dvd_left h _)
  have hl : ¬ (p : ℤ) ∣ f.leadingCoeff := fun h => hN (dvd_mul_of_dvd_right h _)
  refine ⟨?_, separable_mod_prime_of_certificate f a b c hab p hc'⟩
  apply natDegree_map_eq_iff.mpr
  exact Or.inl (by
    simpa only [Int.coe_castRingHom, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] using hl)

end BinaryFormMoat
