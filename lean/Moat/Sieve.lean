import Moat.PeriodicCertificate
import Mathlib.Tactic.FinCases

namespace BinaryFormMoat

/-- Canonical nonnegative representatives of a residue pair. -/
def representative {Q : ℕ} (u : Residue Q) : Point := (u.1.val, u.2.val)

@[simp] theorem residue_representative (Q : ℕ) [NeZero Q] (u : Residue Q) :
    residue Q (representative u) = u := by
  apply Prod.ext <;> simp [residue, representative]

/-- Polynomial evaluation respects congruence of both coordinates. -/
theorem value_cast_congr (F : Form) (Q : ℕ) (z w : Point)
    (h : residue Q z = residue Q w) :
    (value F z : ZMod Q) = (value F w : ZMod Q) := by
  change (Int.castRingHom (ZMod Q)) (MvPolynomial.eval ![z.1, z.2] F) =
    (Int.castRingHom (ZMod Q)) (MvPolynomial.eval ![w.1, w.2] F)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  congr 2
  funext i
  fin_cases i
  · simpa [Function.comp_def, residue] using congrArg Prod.fst h
  · simpa [Function.comp_def, residue] using congrArg Prod.snd h

/-- Reducing a congruence to a divisor of its modulus. -/
theorem residue_eq_of_dvd {Q p : ℕ} (hpQ : p ∣ Q) (z w : Point)
    (h : residue Q z = residue Q w) : residue p z = residue p w := by
  apply Prod.ext
  · have he := congrArg (ZMod.castHom hpQ (ZMod p)) (congrArg Prod.fst h)
    simpa [residue] using he
  · have he := congrArg (ZMod.castHom hpQ (ZMod p)) (congrArg Prod.snd h)
    simpa [residue] using he

/-- A finite periodic superset defined by counting only selected prime divisors. -/
noncomputable def primeSieve (F : Form) (P : Finset ℕ) (Q r : ℕ) (u : Residue Q) : Prop :=
  (P.filter (fun p => p ∣ (value F (representative u)).natAbs)).card ≤ r

/-- The selected-prime sieve contains all vertices of the original problem.
Every selected prime divides the period; zero polynomial values remain excluded by `Allowed`. -/
theorem allowed_primeSieve (F : Form) (P : Finset ℕ) (Q r : ℕ) [NeZero Q]
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ∣ Q)
    (z : Point) (hz : Allowed F r z) : primeSieve F P Q r (residue Q z) := by
  have heq : P.filter (fun p => p ∣ (value F (representative (residue Q z))).natAbs) =
      P.filter (fun p => p ∣ (value F z).natAbs) := by
    apply Finset.filter_congr
    intro p hp
    have he := value_cast_congr F p (representative (residue Q z)) z
      (residue_eq_of_dvd (hPQ p hp) _ _ (residue_representative Q _))
    rw [← Int.natCast_dvd, ← Int.natCast_dvd,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, he]
  unfold primeSieve
  rw [heq]
  exact (selected_prime_count_le P (value F z) hz.1 hP).trans hz.2

end BinaryFormMoat
