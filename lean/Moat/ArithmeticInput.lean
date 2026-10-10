import Moat.GoodReduction
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable

namespace BinaryFormMoat

/-- A positive-degree integer irreducible remains irreducible over the rationals. -/
theorem irreducible_rat_map (p : Polynomial ℤ) (hp : Irreducible p)
    (hdeg : 0 < p.natDegree) : Irreducible (p.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (hp.isPrimitive (by omega))).mp hp

/-- The exact irreducible input of the moat problem gives a separable rational polynomial. -/
theorem irreducible_rat_map_separable (p : Polynomial ℤ) (hp : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) : (p.map (Int.castRingHom ℚ)).Separable :=
  (irreducible_rat_map p hp (by omega)).separable

/-- The irreducible moat input has good reduction outside the divisors of one nonzero integer. -/
theorem irreducible_good_reduction_modulus (f : Polynomial ℤ) (hf : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ N →
      (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree ∧
      (f.map (Int.castRingHom (ZMod p))).Separable :=
  exists_good_reduction_modulus f (by omega) (irreducible_rat_map_separable f hf hdeg)

end BinaryFormMoat
