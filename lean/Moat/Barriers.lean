import Moat.Arithmetic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

namespace BinaryFormMoat

/-- A finite family can be assigned distinct rational primes. -/
theorem exists_injective_primes (ι : Type*) [Fintype ι] :
    ∃ p : ι → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime := by
  let e := Infinite.natEmbedding Nat.Primes
  let f : ι → Nat.Primes := fun i => e (Fintype.equivFin ι i).val
  refine ⟨fun i => (f i).val, ?_, fun i => (f i).property⟩
  intro i j h
  apply (Fintype.equivFin ι).injective
  apply Fin.ext
  exact e.injective (Subtype.ext h)

/-- CRT supplies periodic forbidden intervals of any prescribed width for a fixed
prime-factor budget. The same interval works for all integers, not just a chosen walk. -/
theorem exists_prime_budget_wall (r W : ℕ) :
    ∃ (a : ℤ) (Q : ℕ), 0 < Q ∧
      ∀ n : ℤ, n ≠ 0 → omega n ≤ r → (W : ℤ) ≤ (n - a) % (Q : ℤ) := by
  classical
  let ι := Fin W × Fin (r + 1)
  obtain ⟨p, hinj, hp⟩ := exists_injective_primes ι
  have hcop : Set.Pairwise (Finset.univ : Finset ι) (Function.onFun Nat.Coprime p) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  let c := Nat.chineseRemainderOfFinset (fun i : ι => i.1.val) p Finset.univ
    (fun i _ => (hp i).ne_zero) hcop
  let Q := ∏ i : ι, p i
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => (hp i).pos)
  refine ⟨-(c.val : ℤ), Q, hQ, ?_⟩
  intro n hn hbudget
  by_contra h
  have hmod0 : 0 ≤ (n + (c.val : ℤ)) % (Q : ℤ) := Int.emod_nonneg _ (by omega)
  have hmodW : (n + (c.val : ℤ)) % (Q : ℤ) < W := by simpa using lt_of_not_ge h
  let i : Fin W := ⟨((n + (c.val : ℤ)) % (Q : ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ) = (n + (c.val : ℤ)) % (Q : ℤ) := Int.toNat_of_nonneg hmod0
  have hdiv (j : Fin (r + 1)) : p (i, j) ∣ n.natAbs := by
    have hc : (p (i, j) : ℤ) ∣ (i.val : ℤ) - c.val :=
      (Int.natCast_modEq_iff.mpr (c.property (i, j) (Finset.mem_univ _))).dvd
    have hpQ : p (i, j) ∣ Q := Finset.dvd_prod_of_mem p (Finset.mem_univ (i, j))
    have hpQ' : (p (i, j) : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hpQ
    have hm : (Q : ℤ) ∣ n + (c.val : ℤ) - i.val := by
      rw [hi]
      exact Int.dvd_self_sub_emod
    have hh := dvd_add hc (hpQ'.trans hm)
    have hn' : (p (i, j) : ℤ) ∣ n := by convert hh using 1; ring
    exact Int.natCast_dvd.mp hn'
  have hcard : r + 1 ≤ omega n := by
    let f : Fin (r + 1) → ↥(n.natAbs.primeFactors) := fun j =>
      ⟨p (i, j), Nat.mem_primeFactors.mpr ⟨hp _, hdiv j, Int.natAbs_ne_zero.mpr hn⟩⟩
    have hf : Function.Injective f := by
      intro j k h
      have he := hinj (congrArg Subtype.val h)
      exact congrArg Prod.snd he
    simpa [omega] using Fintype.card_le_of_injective f hf
  omega

/-- A jump no longer than a forbidden interval cannot cross its periodic boundary. -/
theorem wall_cell_eq (Q W x y : ℤ) (hQ : 0 < Q)
    (hx : W ≤ x % Q) (hy : W ≤ y % Q)
    (hxy : x - y ≤ W) (hyx : y - x ≤ W) : x / Q = y / Q := by
  have hx0 := Int.emod_nonneg x (ne_of_gt hQ)
  have hy0 := Int.emod_nonneg y (ne_of_gt hQ)
  have hxQ := Int.emod_lt_of_pos x hQ
  have hyQ := Int.emod_lt_of_pos y hQ
  have hxe := Int.emod_add_mul_ediv x Q
  have hye := Int.emod_add_mul_ediv y Q
  rcases lt_trichotomy (x / Q) (y / Q) with h | h | h
  · have hm : Q * (x / Q + 1) ≤ Q * (y / Q) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hQ)
    nlinarith
  · exact h
  · have hm : Q * (y / Q + 1) ≤ Q * (x / Q) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hQ)
    nlinarith

end BinaryFormMoat
