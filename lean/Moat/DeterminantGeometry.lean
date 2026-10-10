import Moat.RootSieve

namespace BinaryFormMoat

/-- Oriented area of two integer vectors. -/
def determinant (z w : Point) : ℤ := z.1 * w.2 - z.2 * w.1

/-- Agreement of two slope constraints forces divisibility of the determinant.
This works for every modulus, without a Gaussian factorization argument. -/
theorem slope_dvd_determinant (p : ℕ) (ρ : ZMod p) (z w : Point)
    (hz : (z.1 : ZMod p) = ρ * (z.2 : ZMod p))
    (hw : (w.1 : ZMod p) = ρ * (w.2 : ZMod p)) :
    p ∣ (determinant z w).natAbs := by
  rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa only [determinant, Int.cast_sub, Int.cast_mul] using
    determinant_zero_of_same_slope (z.1 : ZMod p) (z.2 : ZMod p)
      (w.1 : ZMod p) (w.2 : ZMod p) ρ hz hw

/-- The product of all common prime constraints divides the determinant. -/
theorem common_prime_product_dvd_determinant (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ρ : (p : ℕ) → ZMod p) (z w : Point)
    (hz : ∀ p ∈ P, (z.1 : ZMod p) = ρ p * (z.2 : ZMod p))
    (hw : ∀ p ∈ P, (w.1 : ZMod p) = ρ p * (w.2 : ZMod p)) :
    (∏ p ∈ P, p) ∣ (determinant z w).natAbs :=
  prime_product_dvd P _ hP fun p hp => slope_dvd_determinant p (ρ p) z w (hz p hp) (hw p hp)

/-- A determinant smaller than the product of its prime divisors is zero. -/
theorem determinant_zero_of_common_primes (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ρ : (p : ℕ) → ZMod p) (z w : Point)
    (hz : ∀ p ∈ P, (z.1 : ZMod p) = ρ p * (z.2 : ZMod p))
    (hw : ∀ p ∈ P, (w.1 : ZMod p) = ρ p * (w.2 : ZMod p))
    (hsmall : (determinant z w).natAbs < ∏ p ∈ P, p) : determinant z w = 0 := by
  have hd := common_prime_product_dvd_determinant P hP ρ z w hz hw
  by_contra hne
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hd
  omega

/-- Twice the area of an axis-aligned rectangle bounds the determinant of two
vectors in that rectangle. Natural absolute values keep all bounds integral. -/
theorem determinant_natAbs_le (z w : Point) (A B : ℕ)
    (hzx : z.1.natAbs ≤ A) (hzy : z.2.natAbs ≤ B)
    (hwx : w.1.natAbs ≤ A) (hwy : w.2.natAbs ≤ B) :
    (determinant z w).natAbs ≤ 2 * A * B := by
  calc
    _ ≤ (z.1 * w.2).natAbs + (z.2 * w.1).natAbs := Int.natAbs_sub_le _ _
    _ = z.1.natAbs * w.2.natAbs + z.2.natAbs * w.1.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ A * B + B * A := Nat.add_le_add (Nat.mul_le_mul hzx hwy) (Nat.mul_le_mul hzy hwx)
    _ = _ := by ring

/-- Hamming disagreement costs at most U per coordinate in the prime product.
No assumption on the number of possible slopes at a coordinate is needed. -/
theorem agreement_product_large (P : Finset ℕ) (ρ σ : (p : ℕ) → ZMod p)
    (U h M : ℕ) (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hamming : (P.filter (fun p => ρ p ≠ σ p)).card ≤ h)
    (hlarge : M * U ^ h < ∏ p ∈ P, p) :
    M < ∏ p ∈ P.filter (fun p => ρ p = σ p), p := by
  classical
  have hdiff : (∏ p ∈ P.filter (fun p => ρ p ≠ σ p), p) ≤ U ^ h := by
    calc
      _ ≤ ∏ _p ∈ P.filter (fun p => ρ p ≠ σ p), U :=
        Finset.prod_le_prod fun p hp => hbound p (Finset.mem_filter.mp hp).1
      _ = U ^ (P.filter (fun p => ρ p ≠ σ p)).card := by simp
      _ ≤ U ^ h := Nat.pow_le_pow_right hU hamming
  have hsplit : (∏ p ∈ P.filter (fun p => ρ p = σ p), p) *
      (∏ p ∈ P.filter (fun p => ρ p ≠ σ p), p) = ∏ p ∈ P, p := by
    exact Finset.prod_filter_mul_prod_filter_not P (fun p => ρ p = σ p) id
  by_contra hn
  have hle := Nat.mul_le_mul (Nat.le_of_not_gt hn) hdiff
  rw [hsplit] at hle
  omega

/-- Nearby root assignments with witnesses in a sufficiently small rectangle
have collinear witnesses. This is the arithmetic separation step for arbitrary
finite root alphabets; expansion of Hamming neighborhoods is a separate task. -/
theorem rectangle_witnesses_collinear (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ σ : (p : ℕ) → ZMod p) (z w : Point) (A B U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hamming : (P.filter (fun p => ρ p ≠ σ p)).card ≤ h)
    (hlarge : (2 * A * B) * U ^ h < ∏ p ∈ P, p)
    (hzx : z.1.natAbs ≤ A) (hzy : z.2.natAbs ≤ B)
    (hwx : w.1.natAbs ≤ A) (hwy : w.2.natAbs ≤ B)
    (hz : ∀ p ∈ P, (z.1 : ZMod p) = ρ p * (z.2 : ZMod p))
    (hw : ∀ p ∈ P, (w.1 : ZMod p) = σ p * (w.2 : ZMod p)) :
    determinant z w = 0 := by
  classical
  apply determinant_zero_of_common_primes (P.filter (fun p => ρ p = σ p))
    (fun p hp => hP p (Finset.mem_filter.mp hp).1) ρ z w
  · intro p hp
    exact hz p (Finset.mem_filter.mp hp).1
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    rw [he]
    exact hw p hp
  · exact (determinant_natAbs_le z w A B hzx hzy hwx hwy).trans_lt
      (agreement_product_large P ρ σ U h (2 * A * B) hU hbound hamming hlarge)

end BinaryFormMoat
