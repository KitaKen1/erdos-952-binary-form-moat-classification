import Moat.LogBudget
import Moat.ArithmeticInput

namespace BinaryFormMoat

/-- Evaluation commutes with the coefficient homomorphism, in the binary
coordinate notation used by the moat graph. -/
theorem value_map_eq_eval₂ {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (F : Form) (z : Point) :
    φ (value F z) = MvPolynomial.eval₂ φ ![φ z.1, φ z.2] F := by
  rw [value, MvPolynomial.eval, MvPolynomial.map_eval₂Hom]
  have hv : (fun i : Fin 2 => φ (![z.1, z.2] i)) = ![φ z.1, φ z.2] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, RingHom.comp_id]
  rfl

/-- The point at infinity in the affine chart is controlled by the top
coefficient; it must not be lost when dividing by the second coordinate. -/
theorem value_homogenize_second_zero (f : Polynomial ℤ) (n : ℕ) (a : ℤ) :
    value (f.homogenize n) (a, 0) = f.coeff n * a ^ n := by
  rw [value_homogenize_eq_sum, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow (Nat.sub_pos_of_lt hk').ne']
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- An irreducible integer polynomial of degree at least two has a
homogenization with no nonzero integer zero. Rational roots and the point at
infinity are both handled, so this is an input-free nonvanishing theorem. -/
theorem irreducible_homogenization_value_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (z : Point)
    (hz : z.1 ≠ 0 ∨ z.2 ≠ 0) : value (f.homogenize f.natDegree) z ≠ 0 := by
  by_cases hb : z.2 = 0
  · have ha : z.1 ≠ 0 := hz.resolve_right (not_not_intro hb)
    have he : z = (z.1, 0) := by ext <;> simp [hb]
    rw [he, value_homogenize_second_zero]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf.ne_zero) (pow_ne_zero _ ha)
  · have hb' : (z.2 : ℚ) ≠ 0 := by exact_mod_cast hb
    have hmap := irreducible_rat_map f hf (by omega)
    have hdegree : (f.map (Int.castRingHom ℚ)).natDegree ≠ 1 := by
      rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective)]
      omega
    have hroot : f.eval₂ (Int.castRingHom ℚ) ((z.1 : ℚ) / (z.2 : ℚ)) ≠ 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using
        (hmap.not_isRoot_of_natDegree_ne_one hdegree (x := (z.1 : ℚ) / (z.2 : ℚ)))
    have he := eval₂_homogenize_on_line f f.natDegree le_rfl (Int.castRingHom ℚ)
      ((z.1 : ℚ) / (z.2 : ℚ)) (z.2 : ℚ)
    rw [div_mul_cancel₀ _ hb'] at he
    intro hzero
    have hz' : (Int.castRingHom ℚ) (value (f.homogenize f.natDegree) z) = 0 := by
      rw [hzero, map_zero]
    rw [value_map_eq_eval₂] at hz'
    have hp : f.eval₂ (Int.castRingHom ℚ) ((z.1 : ℚ) / (z.2 : ℚ)) *
        (z.2 : ℚ) ^ f.natDegree = 0 := he.symm.trans hz'
    exact (mul_ne_zero hroot (pow_ne_zero _ hb')) hp

end BinaryFormMoat
