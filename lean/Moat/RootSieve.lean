import Moat.Arithmetic
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

namespace BinaryFormMoat

/-- Homogenized evaluation on a root line. This includes the point (0,0), so
no primitivity or invertibility of the second coordinate is required. -/
theorem eval₂_homogenize_on_line {R K : Type*} [CommSemiring R] [CommSemiring K]
    (f : Polynomial R) (n : ℕ) (hn : f.natDegree ≤ n) (φ : R →+* K) (ρ b : K) :
    MvPolynomial.eval₂ φ ![ρ * b, b] (f.homogenize n) = f.eval₂ φ ρ * b ^ n := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => MvPolynomial.eval₂ φ ![ρ * b, b] (f.homogenize n) =
      f.eval₂ φ ρ * b ^ n) n
  · simp
  · intro k a _ hk
    simp only [Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow hk,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [mul_pow]
    calc
      _ = φ a * ρ ^ k * (b ^ k * b ^ (n - k)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hk]
  · intro p q _ _ hp hq
    simp [hp, hq, add_mul]
  · exact hn

/-- A root selected modulo p defines an integer lattice whose points have
p dividing the homogenized value. No degree-preservation hypothesis is needed. -/
theorem root_line_dvd_value (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (p : ℕ) (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hz : (z.1 : ZMod p) = ρ * (z.2 : ZMod p)) :
    p ∣ (value (f.homogenize n) z).natAbs := by
  rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod p)) (MvPolynomial.eval ![z.1, z.2] _) = 0
  rw [MvPolynomial.eval, MvPolynomial.map_eval₂Hom]
  have hv : (fun i : Fin 2 => (Int.castRingHom (ZMod p)) (![z.1, z.2] i)) =
      ![(z.1 : ZMod p), (z.2 : ZMod p)] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, RingHom.comp_id]
  change MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
    ![(z.1 : ZMod p), (z.2 : ZMod p)] (f.homogenize n) = 0
  rw [hz, eval₂_homogenize_on_line f n hn, hρ, zero_mul]

/-- Distinct rational primes dividing an integer also divide it as a product. -/
theorem prime_product_dvd (P : Finset ℕ) (n : ℤ) (hP : ∀ p ∈ P, p.Prime)
    (hn : ∀ p ∈ P, p ∣ n.natAbs) : (∏ p ∈ P, p) ∣ n.natAbs := by
  by_cases hzero : n = 0
  · simp [hzero]
  · have hsub : P ⊆ n.natAbs.primeFactors := by
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨hP p hp, hn p hp, Int.natAbs_ne_zero.mpr hzero⟩
    exact (Finset.prod_dvd_prod_of_subset P n.natAbs.primeFactors id hsub).trans
      n.natAbs.prod_primeFactors_dvd

/-- All selected root-line hits consume the ordinary distinct-prime budget. -/
theorem root_line_hit_count_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ρ : (p : ℕ) → ZMod p)
    (hρ : ∀ p ∈ P, f.eval₂ (Int.castRingHom (ZMod p)) (ρ p) = 0)
    (z : Point) (hz : value (f.homogenize n) z ≠ 0) :
    (P.filter (fun p => (z.1 : ZMod p) = ρ p * (z.2 : ZMod p))).card ≤
      omega (value (f.homogenize n) z) := by
  classical
  apply le_trans (Finset.card_le_card ?_) (selected_prime_count_le P _ hz hP)
  intro p hp
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, root_line_dvd_value f n hn p (ρ p) (hρ p hp) z he⟩

/-- Primitive directions stay nonzero modulo every prime. Primitivity is only
needed for the direction, not for the arbitrary lattice points in the moat graph. -/
theorem primitive_direction_mod_prime (a b : ℤ) (hab : IsCoprime a b)
    (p : ℕ) [Fact p.Prime] : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hab
  by_contra h
  push Not at h
  have he : (u : ZMod p) * (a : ZMod p) + (v : ZMod p) * (b : ZMod p) = 1 := by
    have he' : ((u * a + v * b : ℤ) : ZMod p) = 1 := by rw [huv, Int.cast_one]
    simpa only [Int.cast_add, Int.cast_mul] using he'
  simp only [h.1, h.2, mul_zero, zero_add] at he
  exact zero_ne_one he

/-- If the primitive direction misses a selected slope but an integer multiple
hits it, that prime must divide the integer multiplier. -/
theorem multiplier_dvd_of_slope_miss (p : ℕ) [Fact p.Prime] (ρ : ZMod p)
    (a b t : ℤ) (hmiss : (a : ZMod p) ≠ ρ * (b : ZMod p))
    (hhit : ((t * a : ℤ) : ZMod p) = ρ * ((t * b : ℤ) : ZMod p)) :
    p ∣ t.natAbs := by
  rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have he : (t : ZMod p) * ((a : ZMod p) - ρ * (b : ZMod p)) = 0 := by
    push_cast at hhit
    calc
      _ = (t : ZMod p) * (a : ZMod p) - ρ * ((t : ZMod p) * (b : ZMod p)) := by ring
      _ = 0 := sub_eq_zero.mpr hhit
  exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hmiss)

/-- A whole batch of root-line constraints gives product divisibility. -/
theorem root_line_product_dvd_value (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ρ : (p : ℕ) → ZMod p)
    (hρ : ∀ p ∈ P, f.eval₂ (Int.castRingHom (ZMod p)) (ρ p) = 0)
    (z : Point) (hz : ∀ p ∈ P, (z.1 : ZMod p) = ρ p * (z.2 : ZMod p)) :
    (∏ p ∈ P, p) ∣ (value (f.homogenize n) z).natAbs :=
  prime_product_dvd P _ hP fun p hp => root_line_dvd_value f n hn p (ρ p) (hρ p hp) z (hz p hp)

/-- Every missed slope must be paid for by a distinct prime factor of the
multiplier. This is the fixed-line witness size input. -/
theorem missed_prime_product_dvd_multiplier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ : (p : ℕ) → ZMod p) (a b t : ℤ)
    (hhit : ∀ p ∈ P, ((t * a : ℤ) : ZMod p) = ρ p * ((t * b : ℤ) : ZMod p)) :
    (∏ p ∈ P.filter (fun p => (a : ZMod p) ≠ ρ p * (b : ZMod p)), p) ∣ t.natAbs := by
  classical
  apply prime_product_dvd _ _ (fun p hp => hP p (Finset.mem_filter.mp hp).1)
  intro p hp
  obtain ⟨hp, hmiss⟩ := Finset.mem_filter.mp hp
  let : Fact p.Prime := ⟨hP p hp⟩
  exact multiplier_dvd_of_slope_miss p (ρ p) a b t hmiss (hhit p hp)

/-- A nonzero witness on a fixed line has multiplier at least the product of
the primes whose selected slopes miss that direction. -/
theorem missed_prime_product_le_multiplier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ : (p : ℕ) → ZMod p) (a b t : ℤ) (ht : t ≠ 0)
    (hhit : ∀ p ∈ P, ((t * a : ℤ) : ZMod p) = ρ p * ((t * b : ℤ) : ZMod p)) :
    (∏ p ∈ P.filter (fun p => (a : ZMod p) ≠ ρ p * (b : ZMod p)), p) ≤ t.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr ht) (missed_prime_product_dvd_multiplier P hP ρ a b t hhit)

end BinaryFormMoat
