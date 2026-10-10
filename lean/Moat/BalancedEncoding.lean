import Moat.FiniteSampling
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace BinaryFormMoat

section Encoding

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    {K B : ι → Type*} [∀ i, Fintype (K i)] [∀ i, Fintype (B i)]

/-- Each root gets exactly one code for each auxiliary label. The entire
product encoding is injective, even when the root types depend on the prime. -/
def blockEncoding (e : ∀ i, K i × A ↪ B i) :
    ((∀ i, K i) × (ι → A)) ↪ (∀ i, B i) where
  toFun x i := e i (x.1 i, x.2 i)
  inj' := by
    intro x y h
    have he : ∀ i, (x.1 i, x.2 i) = (y.1 i, y.2 i) :=
      fun i => (e i).injective (congrFun h i)
    exact Prod.ext (funext fun i => congrArg Prod.fst (he i))
      (funext fun i => congrArg Prod.snd (he i))

/-- The lift of an event includes every auxiliary label, so conditioning on
accepted codes preserves the original uniform root law exactly. -/
def encodedEvent (e : ∀ i, K i × A ↪ B i) (E : Finset (∀ i, K i)) :
    Finset (∀ i, B i) := (E ×ˢ Finset.univ).map (blockEncoding e)

omit [∀ i, Fintype (K i)] [∀ i, Fintype (B i)] in
theorem card_encodedEvent (e : ∀ i, K i × A ↪ B i) (E : Finset (∀ i, K i)) :
    (encodedEvent e E).card = E.card * Fintype.card A ^ Fintype.card ι := by
  simp [encodedEvent]

omit [∀ i, Fintype (B i)] in
/-- No approximate mean or change of root distribution is needed. -/
theorem encodedEvent_conditional_fraction (e : ∀ i, K i × A ↪ B i)
    (hA : 0 < Fintype.card A) (E : Finset (∀ i, K i)) :
    ((encodedEvent e E).card : ℝ) / (encodedEvent e Finset.univ).card =
      (E.card : ℝ) / Fintype.card (∀ i, K i) := by
  rw [card_encodedEvent, card_encodedEvent]
  simp only [Finset.card_univ, Nat.cast_mul, Nat.cast_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero _ (by exact_mod_cast hA.ne'))

/-- Ambient cube density is the original event probability times the
acceptance density. This also accounts for all rejected codes. -/
theorem encodedEvent_ambient_fraction (e : ∀ i, K i × A ↪ B i)
    (hK : 0 < Fintype.card (∀ i, K i)) (E : Finset (∀ i, K i)) :
    ((encodedEvent e E).card : ℝ) / Fintype.card (∀ i, B i) =
      ((E.card : ℝ) / Fintype.card (∀ i, K i)) *
        ((encodedEvent e Finset.univ).card / (Fintype.card (∀ i, B i) : ℝ)) := by
  rw [card_encodedEvent, card_encodedEvent]
  simp only [Finset.card_univ, Nat.cast_mul, Nat.cast_pow]
  have hK' : (Fintype.card (∀ i, K i) : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hK']

end Encoding

/-- A b-bit block contains floor(2^b/d) disjoint codes for every one of d
roots. The unused codes are kept outside the accepted sample space. -/
theorem exists_balanced_binary_embedding (K : Type*) [Fintype K]
    (d b : ℕ) (hK : Fintype.card K = d) :
    Nonempty (K × Fin (2 ^ b / d) ↪ (Fin b → Bool)) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa [Fintype.card_prod, Fintype.card_fun, hK] using Nat.mul_div_le (2 ^ b) d

/-- Exact acceptance density in the full binary cube of b*k bits. -/
theorem binary_acceptance_fraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] (d b m : ℕ)
    (hK : ∀ i, Fintype.card (K i) = d)
    (e : ∀ i, K i × Fin m ↪ (Fin b → Bool)) :
    ((encodedEvent e Finset.univ).card : ℝ) /
      Fintype.card (ι → Fin b → Bool) =
        ((d : ℝ) * m / 2 ^ b) ^ Fintype.card ι := by
  rw [card_encodedEvent]
  simp [Fintype.card_pi, hK, mul_pow, div_pow]

/-- The cost of discarding the incomplete final group of codes is at most
d/Q per block. The bound is valid independently of a chosen encoding. -/
theorem balanced_block_fraction_lower (d Q : ℕ) (hd : 0 < d) (hQ : 0 < Q) :
    1 - (d : ℝ) / Q ≤ ((d * (Q / d) : ℕ) : ℝ) / Q := by
  have hnat : Q ≤ d * (Q / d) + d := by
    have hmod := Nat.mod_lt Q hd
    have he := Nat.mod_add_div Q d
    omega
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ
  apply (le_div_iff₀ hQ').mpr
  have hnat' : (Q : ℝ) ≤ (d * (Q / d) : ℕ) + d := by exact_mod_cast hnat
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hQ'.ne']
  linarith

end BinaryFormMoat
