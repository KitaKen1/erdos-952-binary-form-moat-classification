import Moat.Basic

namespace BinaryFormMoat

@[simp] theorem value_mul (F G : Form) (z : Point) :
    value (F * G) z = value F z * value G z := by
  simp [value]

/-- Distinct prime counts are monotone under divisibility of a nonzero value. -/
theorem omega_le_of_dvd {a b : ℤ} (hab : a ∣ b) (hb : b ≠ 0) : omega a ≤ omega b := by
  apply Finset.card_le_card
  exact Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr hab) (Int.natAbs_ne_zero.mpr hb)

/-- Passing to a polynomial divisor only enlarges the allowed vertex set. -/
theorem allowed_of_dvd {F G : Form} (hGF : G ∣ F) (r : ℕ) (z : Point)
    (hz : Allowed F r z) : Allowed G r z := by
  obtain ⟨H, rfl⟩ := hGF
  have he := hz.1
  rw [value_mul] at he
  refine ⟨(mul_ne_zero_iff.mp he).1, ?_⟩
  exact (omega_le_of_dvd (dvd_mul_right (value G z) (value H z)) he).trans
    (by simpa only [value_mul] using hz.2)

/-- A fixed change of budget preserves transport of uniform component bounds. -/
theorem uniformMoat_of_budget_domination (F G : Form) (budget : ℕ → ℕ)
    (hsub : ∀ r z, Allowed F r z → Allowed G (budget r) z) (hG : UniformMoat G) :
    UniformMoat F := by
  intro R r
  obtain ⟨B, hB⟩ := hG R (budget r)
  refine ⟨B, ?_⟩
  let inc : {z : Point // Allowed F r z} → {z : Point // Allowed G (budget r) z} :=
    fun z => ⟨z.val, hsub r z.val z.property⟩
  have hi : Function.Injective inc := by
    intro x y h
    have he : (inc x).val = (inc y).val := congrArg Subtype.val h
    exact Subtype.ext he
  let hom : graph F r R →g graph G (budget r) R :=
    { toFun := inc
      map_rel' := by
        intro x y h
        exact ⟨fun he => h.1 (hi he), h.2⟩ }
  intro z
  apply le_trans _ (hB (inc z))
  apply Set.encard_le_encard_of_injOn (f := inc)
  · intro w hw
    exact hw.map hom
  · exact hi.injOn

/-- Any pointwise inclusion of the allowed sets transports uniform component bounds. -/
theorem uniformMoat_of_allowed_subset (F G : Form)
    (hsub : ∀ r z, Allowed F r z → Allowed G r z) (hG : UniformMoat G) :
    UniformMoat F := uniformMoat_of_budget_domination F G id hsub hG

/-- A single divisor with the moat property suffices for the whole polynomial. -/
theorem uniformMoat_of_dvd (F G : Form) (hGF : G ∣ F) (hG : UniformMoat G) :
    UniformMoat F :=
  uniformMoat_of_allowed_subset F G (allowed_of_dvd hGF) hG

/-- Positive powers have exactly the same admissible lattice points. -/
theorem allowed_pow_iff (F : Form) (m r : ℕ) (hm : m ≠ 0) (z : Point) :
    Allowed (F^m) r z ↔ Allowed F r z := by
  simp [Allowed, value, omega, pow_ne_zero_iff hm, Int.natAbs_pow,
    Nat.primeFactors_pow _ hm]

/-- Taking a positive power leaves the uniform moat property unchanged. -/
theorem uniformMoat_pow_iff (F : Form) (m : ℕ) (hm : m ≠ 0) :
    UniformMoat (F^m) ↔ UniformMoat F := by
  constructor
  · intro h
    exact uniformMoat_of_allowed_subset F (F^m)
      (fun r z hz => (allowed_pow_iff F m r hm z).mpr hz) h
  · intro h
    exact uniformMoat_of_allowed_subset (F^m) F
      (fun r z hz => (allowed_pow_iff F m r hm z).mp hz) h

/-- Multiplication adds at most the two distinct-prime budgets. -/
theorem omega_mul_le (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    omega (a * b) ≤ omega a + omega b := by
  simp only [omega, Int.natAbs_mul,
    Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)]
  exact Finset.card_union_le _ _

/-- Nonzero coefficient content does not change the all-budgets moat property. -/
theorem uniformMoat_const_mul_iff (F : Form) (c : ℤ) (hc : c ≠ 0) :
    UniformMoat (MvPolynomial.C c * F) ↔ UniformMoat F := by
  constructor
  · intro h
    apply uniformMoat_of_budget_domination F (MvPolynomial.C c * F)
      (fun r => r + omega c) _ h
    intro r z hz
    have he : value (MvPolynomial.C c * F) z = c * value F z := by simp [value]
    refine ⟨?_, ?_⟩
    · rw [he]
      exact mul_ne_zero hc hz.1
    · rw [he]
      calc
        omega (c * value F z) ≤ omega c + omega (value F z) := omega_mul_le _ _ hc hz.1
        _ ≤ omega c + r := Nat.add_le_add_left hz.2 _
        _ = r + omega c := Nat.add_comm _ _
  · exact uniformMoat_of_dvd _ F (dvd_mul_left F (MvPolynomial.C c))

end BinaryFormMoat
