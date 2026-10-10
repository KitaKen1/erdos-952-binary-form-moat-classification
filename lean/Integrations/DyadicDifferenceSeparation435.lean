import Integrations.DifferenceSeparation435
import Moat.RectangleParameters

noncomputable section

namespace BinaryFormMoat.GeometryIntegration

/-- A deterministic comparison with the true prime-log mean. It avoids
sampling-without-replacement product concentration when g*log(T)>=log(2). -/
theorem dyadic_log_mean_bounds (P : Finset ℕ) (hne : P.Nonempty) (T : ℕ) (hT : 0 < T)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T) :
    Real.log (T : ℝ) ≤ (∑ p ∈ P, Real.log (p : ℝ)) / P.card ∧
      (∑ p ∈ P, Real.log (p : ℝ)) / P.card ≤ Real.log (T : ℝ) + Real.log 2 := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  constructor
  · exact (le_div_iff₀ hc).mpr (by
      simpa only [mul_comm] using dyadic_prime_log_sum_lower P T hT hlo)
  · apply (div_le_iff₀ hc).mpr
    have hs : (∑ p ∈ P, Real.log (p : ℝ)) ≤ (P.card : ℝ) * Real.log (2 * T : ℕ) := by
      calc
        _ ≤ ∑ _p ∈ P, Real.log (2 * T : ℕ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact Real.log_le_log (by exact_mod_cast (hT.trans_le (hlo p hp)))
            (by exact_mod_cast hhi p hp)
        _ = _ := by simp
    rw [Nat.cast_mul, Real.log_mul (by norm_num)
      (by exact_mod_cast (Nat.ne_of_gt hT)), Nat.cast_ofNat] at hs
    nlinarith only [hs]

theorem dyadic_log_mean_lower_end_loss (P : Finset ℕ) (hne : P.Nonempty) (T : ℕ) (hT : 0 < T)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (g : ℝ) (hg : 0 ≤ g) (hmargin : Real.log 2 ≤ g * Real.log (T : ℝ)) :
    (1 - g) * ((∑ p ∈ P, Real.log (p : ℝ)) / P.card) ≤ Real.log (T : ℝ) := by
  obtain ⟨hl, hu⟩ := dyadic_log_mean_bounds P hne T hT hlo hhi
  have hm := mul_le_mul_of_nonneg_left hl hg
  nlinarith only [hu, hmargin, hm]

/-- Any selected subset in the dyadic batch satisfies the arithmetic gap
and product inputs from deterministic lower-end bounds. No exceptional
prime-product event or probabilistic product premise is required. -/
theorem walk_difference_separation_dyadic_exp_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 2 ≤ q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (T : ℕ) (hT : 2 ≤ T) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (η : ℝ) (hη : 0 ≤ η) (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hsize : Real.log (max 1 (4 * (D * N)) : ℕ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
        (1 - η) * P.card * Real.log (T : ℝ))
    (harea : 16 * prefixArea z N < T ^ ((2 * q - 4) * l)) :
    let b := 16 * f.natDegree * q ^ 2 + 4
    ((nonInjectiveRootAssignments (pointDifferences (walkVertexSet z N)) P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) ≤ Real.exp (-(l : ℝ) / (4 * (b * q : ℕ))) := by
  apply walk_difference_separation_exp_tail f hf hd z D N hstep P hP S hcard hroot q l
    (by omega) hl hcount T hT hhi η hη hschedule
  · exact rectangle_log_gap_of_dyadic_lower P T (by omega) hlo _ η hsize
  · have he : 2 * (8 * prefixArea z N) * 1 = 16 * prefixArea z N := by ring
    have h := rectangle_separation_of_dyadic_bounds P T q l (8 * prefixArea z N) 1
      hT hq hcount hlo (by rw [he]; exact harea)
    rwa [he] at h

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.dyadic_log_mean_bounds
#print axioms BinaryFormMoat.GeometryIntegration.dyadic_log_mean_lower_end_loss
#print axioms BinaryFormMoat.GeometryIntegration.walk_difference_separation_dyadic_exp_tail
