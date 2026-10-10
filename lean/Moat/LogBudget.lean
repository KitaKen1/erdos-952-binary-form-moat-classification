import Moat.RootSieve
import Moat.FiniteSampling
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BinaryFormMoat

/-- An explicit coefficient constant, chosen positive even for the zero polynomial. -/
def coefficientBound (f : Polynomial ℤ) (n : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.range (n + 1), (f.coeff k).natAbs

/-- The usual binary homogeneous expansion, including zero coordinates. -/
theorem value_homogenize_eq_sum (f : Polynomial ℤ) (n : ℕ) (z : Point) :
    value (f.homogenize n) z =
      ∑ k ∈ Finset.range (n + 1), f.coeff k * z.1 ^ k * z.2 ^ (n - k) := by
  simp only [value, Polynomial.homogenize, map_sum, MvPolynomial.eval_monomial,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, mul_assoc]

/-- The absolute value of a degree-n homogenization in a box is at most
C_f times the nth power of the box radius, with an explicit positive C_f. -/
theorem homogenized_value_growth (f : Polynomial ℤ) (n : ℕ) (z : Point) (A : ℕ)
    (hza : z.1.natAbs ≤ A) (hzb : z.2.natAbs ≤ A) :
    (value (f.homogenize n) z).natAbs ≤ coefficientBound f n * A ^ n := by
  rw [value_homogenize_eq_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), (f.coeff k * z.1 ^ k * z.2 ^ (n - k)).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (f.coeff k).natAbs * A ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [Int.natAbs_mul, Int.natAbs_pow]
      calc
        _ ≤ (f.coeff k).natAbs * A ^ k * A ^ (n - k) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hza k))
            (Nat.pow_le_pow_left hzb (n - k))
        _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk']
    _ ≤ coefficientBound f n * A ^ n := by
      rw [← Finset.sum_mul]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- Dividing logarithmic growth by the degree cancels its contribution to
the radius term. The coefficient cost is retained explicitly. -/
theorem log_homogenized_value_div_degree_le (f : Polynomial ℤ) (n : ℕ) (hn : 0 < n)
    (z : Point) (hz : value (f.homogenize n) z ≠ 0) (A : ℕ) (hA : 0 < A)
    (hza : z.1.natAbs ≤ A) (hzb : z.2.natAbs ≤ A) :
    Real.log ((value (f.homogenize n) z).natAbs : ℝ) / n ≤
      Real.log (A : ℝ) + Real.log (coefficientBound f n : ℝ) / n := by
  have hpos : 0 < ((value (f.homogenize n) z).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hz
  have hC : (coefficientBound f n : ℝ) ≠ 0 := by
    have : 0 < coefficientBound f n := by unfold coefficientBound; omega
    exact_mod_cast this.ne'
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbound : ((value (f.homogenize n) z).natAbs : ℝ) ≤
      (coefficientBound f n : ℝ) * (A : ℝ) ^ n := by
    exact_mod_cast homogenized_value_growth f n z A hza hzb
  calc
    _ ≤ Real.log ((coefficientBound f n : ℝ) * (A : ℝ) ^ n) / n :=
      div_le_div_of_nonneg_right (Real.log_le_log hpos hbound) (Nat.cast_nonneg n)
    _ = _ := by
      rw [Real.log_mul hC (pow_ne_zero _ hA'), Real.log_pow, add_div,
        mul_div_cancel_left₀ _ hn', add_comm]

/-- The logarithmic mass of distinct selected prime divisors is bounded by
the logarithm of the absolute value of a nonzero integer. -/
theorem log_prime_product_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℤ) (hn : n ≠ 0) (hdiv : ∀ p ∈ P, p ∣ n.natAbs) :
    (∑ p ∈ P, Real.log (p : ℝ)) ≤ Real.log (n.natAbs : ℝ) := by
  have hpos : 0 < (∏ p ∈ P, (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hP p hp).pos
  have hle : (∏ p ∈ P, (p : ℝ)) ≤ (n.natAbs : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (prime_product_dvd P n hP hdiv)
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_prod (fun p hp => by exact_mod_cast (hP p hp).ne_zero)] at hlog
  exact hlog

/-- For a primitive direction, the sum of uniform root-hit rates weighted by
log p is at most log |F(a,b)| / d when each prime supplies d roots.
This captures the arithmetic cancellation without a Gaussian norm argument. -/
theorem mean_log_root_hits_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (d : ℕ) (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize n) z ≠ 0) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      (((S p).filter (fun ρ => (z.1 : ZMod p) = ρ * (z.2 : ZMod p))).card : ℝ) /
        (S p).card) ≤ Real.log ((value (f.homogenize n) z).natAbs : ℝ) / d := by
  classical
  calc
    _ ≤ ∑ p ∈ P, if p ∣ (value (f.homogenize n) z).natAbs
        then Real.log (p : ℝ) / d else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      let : Fact p.Prime := ⟨hP p hp⟩
      by_cases hdiv : p ∣ (value (f.homogenize n) z).natAbs
      · rw [ite_eq_left hdiv]
        have he := mul_le_mul_of_nonneg_left
          (uniform_slope_hit_bound (S p) (z.1 : ZMod p) (z.2 : ZMod p)
            (primitive_direction_mod_prime z.1 z.2 hprim p)) (Real.log_natCast_nonneg p)
        simpa only [← mul_div_assoc, mul_one, hcard p hp] using he
      · rw [ite_eq_right hdiv]
        have hempty : (S p).filter (fun ρ => (z.1 : ZMod p) = ρ * (z.2 : ZMod p)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro ρ hρ
          obtain ⟨hmem, hhit⟩ := Finset.mem_filter.mp hρ
          exact hdiv (root_line_dvd_value f n hn p ρ (hroot p hp ρ hmem) z hhit)
        simp [hempty]
    _ = (∑ p ∈ P.filter (fun p => p ∣ (value (f.homogenize n) z).natAbs),
          Real.log (p : ℝ)) / d := by rw [← Finset.sum_filter, Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (log_prime_product_le _ (fun p hp => hP p (Finset.mem_filter.mp hp).1) _ hz
        (fun _ hp => (Finset.mem_filter.mp hp).2)) (Nat.cast_nonneg d)

/-- The previous marginal calculation is the actual average over a single
uniform product of all root choices in the batch. The positive root count
ensures this product sample space is nonempty. -/
theorem average_log_root_hits_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (d : ℕ) (hd : 0 < d) (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize n) z ≠ 0) :
    (∑ σ ∈ Fintype.piFinset (fun p : P => S p), ∑ p : P,
      if (z.1 : ZMod p.val) = σ p * (z.2 : ZMod p.val) then Real.log (p.val : ℝ) else 0) /
        (Fintype.piFinset (fun p : P => S p)).card ≤
      Real.log ((value (f.homogenize n) z).natAbs : ℝ) / d := by
  classical
  have hS : ∀ p : P, (S p).Nonempty := by
    intro p
    apply Finset.card_pos.mp
    rw [hcard p p.property]
    exact hd
  rw [box_average_weighted_hits (fun p : P => S p) hS
    (fun p ρ => (z.1 : ZMod p.val) = ρ * (z.2 : ZMod p.val))
    (fun p => Real.log (p.val : ℝ))]
  simp_rw [← mul_div_assoc]
  exact (Finset.sum_coe_sort P (fun p : ℕ => Real.log (p : ℝ) *
    (((S p).filter (fun ρ => (z.1 : ZMod p) = ρ * (z.2 : ZMod p))).card : ℝ) /
    (S p).card)).le.trans (mean_log_root_hits_le f n hn P hP S d hcard hroot z hprim hz)

/-- The complete fixed-direction mean bound: averaging over all d-root choices
costs at most log A plus a coefficient constant divided by d. Concentration,
Hamming expansion, and walk-uniform scheduling are not asserted here. -/
theorem average_log_root_hits_growth_le (f : Polynomial ℤ) (d : ℕ)
    (hdeg : f.natDegree ≤ d) (hd : 0 < d)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize d) z ≠ 0)
    (A : ℕ) (hA : 0 < A) (hza : z.1.natAbs ≤ A) (hzb : z.2.natAbs ≤ A) :
    (∑ σ ∈ Fintype.piFinset (fun p : P => S p), ∑ p : P,
      if (z.1 : ZMod p.val) = σ p * (z.2 : ZMod p.val) then Real.log (p.val : ℝ) else 0) /
        (Fintype.piFinset (fun p : P => S p)).card ≤
      Real.log (A : ℝ) + Real.log (coefficientBound f d : ℝ) / d :=
  (average_log_root_hits_le f d hdeg P hP S d hd hcard hroot z hprim hz).trans
    (log_homogenized_value_div_degree_le f d hd z hz A hA hza hzb)

end BinaryFormMoat
