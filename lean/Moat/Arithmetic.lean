import Moat.Basic

namespace BinaryFormMoat

/-- A nonzero direction is killed by at most one slope over a field.
For primitive integer directions modulo a prime, the nonzero hypothesis holds. -/
theorem slope_unique {K : Type*} [Field K] (a b ρ σ : K)
    (hab : a ≠ 0 ∨ b ≠ 0) (hρ : a = ρ * b) (hσ : a = σ * b) : ρ = σ := by
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by simpa [hb] using hρ
    exact hab.elim (fun h => h ha) (fun h => h hb)
  exact mul_right_cancel₀ hb (hρ.symm.trans hσ)

/-- Two vectors killed by the same slope have determinant zero in the residue field. -/
theorem determinant_zero_of_same_slope {K : Type*} [CommRing K] (a b c d ρ : K)
    (hv : a = ρ * b) (hw : c = ρ * d) : a * d - b * c = 0 := by
  rw [hv, hw]
  ring

/-- A selected set of prime divisors never exceeds the distinct-prime budget. -/
theorem selected_prime_count_le (P : Finset ℕ) (n : ℤ) (hn : n ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) :
    (P.filter (fun p => p ∣ n.natAbs)).card ≤ omega n := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hP p hpP, hpn, Int.natAbs_ne_zero.mpr hn⟩

end BinaryFormMoat
