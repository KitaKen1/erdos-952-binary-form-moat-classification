import Moat.Normalization
import Mathlib.Algebra.Field.ZMod

namespace BinaryFormMoat
open Polynomial

/-- Number of distinct roots modulo p. All applications below require p prime, so the
root set is finite. The definition itself does not require a typeclass proof of primality. -/
noncomputable def rootCountMod (f : Polynomial ℤ) (p : ℕ) : ℕ :=
  Nat.card {x : ZMod p // f.eval₂ (Int.castRingHom (ZMod p)) x = 0}

/-- A canonical finite root alphabet at every prime, and the empty set elsewhere.
Unlike `Polynomial.roots`, this definition also handles the zero reduction. -/
noncomputable def primeRootSet (f : Polynomial ℤ) (p : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    Finset.univ.filter (fun x => f.eval₂ (Int.castRingHom (ZMod p)) x = 0)
  else ∅

theorem mem_primeRootSet (f : Polynomial ℤ) (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    x ∈ primeRootSet f p ↔ f.eval₂ (Int.castRingHom (ZMod p)) x = 0 := by
  classical
  simp [primeRootSet, hp]

theorem card_primeRootSet (f : Polynomial ℤ) (p : ℕ) (hp : p.Prime) :
    (primeRootSet f p).card = rootCountMod f p := by
  classical
  have he : {x : ZMod p | f.eval₂ (Int.castRingHom (ZMod p)) x = 0} =
      (primeRootSet f p : Set (ZMod p)) := by
    ext x
    exact (mem_primeRootSet f p hp x).symm
  symm
  change Nat.card ↥{x : ZMod p | f.eval₂ (Int.castRingHom (ZMod p)) x = 0} = _
  rw [Nat.card_coe_set_eq, he, Set.ncard_coe_finset]

/-- At a prime, the root count agrees with the usual finite set of polynomial roots. -/
theorem rootCountMod_eq_roots (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (hf : f.map (Int.castRingHom (ZMod p)) ≠ 0) :
    rootCountMod f p = (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  classical
  have he : {x : ZMod p | f.eval₂ (Int.castRingHom (ZMod p)) x = 0} =
      ((f.map (Int.castRingHom (ZMod p))).roots.toFinset : Set (ZMod p)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots hf, Polynomial.IsRoot, Polynomial.eval_map]
  change Nat.card ↥{x : ZMod p | f.eval₂ (Int.castRingHom (ZMod p)) x = 0} = _
  rw [Nat.card_coe_set_eq, he, Set.ncard_coe_finset]

/-- Outside the leading-coefficient divisors, monic normalization preserves root count. -/
theorem rootCountMod_normalization (f : Polynomial ℤ) (hdeg : 1 ≤ f.natDegree)
    (p : ℕ) [Fact p.Prime] (hl : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0) :
    rootCountMod f p = rootCountMod f.integralNormalization p :=
  Nat.card_congr (normalizedRootEquiv f hdeg (Int.castRingHom (ZMod p)) hl)

end BinaryFormMoat
