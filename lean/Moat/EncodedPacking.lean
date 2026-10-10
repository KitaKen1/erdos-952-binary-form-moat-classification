import Moat.EncodedRootTail
import Moat.EncodedSeparation
import Moat.HammingPacking

namespace BinaryFormMoat

/-- Flatten the block coordinates to the b*k individual Boolean coordinates. -/
def bitEncoding {ι A : Type*} {K : ι → Type*} (b : ℕ)
    (e : ∀ i, K i × A ↪ (Fin b → Bool)) :
    ((∀ i, K i) × (ι → A)) ↪ (ι × Fin b → Bool) where
  toFun x q := blockEncoding e x q.1 q.2
  inj' := by
    intro x y h
    apply (blockEncoding e).injective
    exact funext fun i => funext fun j => congrFun h (i, j)

def encodedBitEvent {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    {K : ι → Type*} (b : ℕ) (e : ∀ i, K i × A ↪ (Fin b → Bool))
    (E : Finset (∀ i, K i)) : Finset (ι × Fin b → Bool) :=
  (E ×ˢ Finset.univ).map (bitEncoding b e)

theorem card_encodedBitEvent {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    {K : ι → Type*} (b : ℕ) (e : ∀ i, K i × A ↪ (Fin b → Bool))
    (E : Finset (∀ i, K i)) :
    (encodedBitEvent b e E).card = (encodedEvent e E).card := by
  simp [encodedBitEvent, encodedEvent]

theorem encodedBitEvent_biUnion {ι A J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq J] {K : ι → Type*} [∀ i, DecidableEq (K i)]
    (b : ℕ) (e : ∀ i, K i × A ↪ (Fin b → Bool))
    (s : Finset J) (E : J → Finset (∀ i, K i)) :
    encodedBitEvent b e (s.biUnion E) = s.biUnion (fun j => encodedBitEvent b e (E j)) := by
  ext z
  simp only [encodedBitEvent, Finset.mem_map, Finset.mem_product, Finset.mem_univ,
    and_true, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, ⟨j, hj, hx⟩, he⟩
    exact ⟨j, hj, x, hx, he⟩
  · rintro ⟨j, hj, x, hx, he⟩
    exact ⟨x, ⟨j, hj, hx⟩, he⟩

/-- Concrete arithmetic packing for a finite family of distinct rational
lines. Only the quantitative neighborhood expansion is left as an input. -/
theorem encoded_line_packing {J : Type*} [DecidableEq J]
    (s : Finset J) (z : J → Point) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool)) (R U r : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : (2 * R * R) * U ^ (2 * r) < ∏ p ∈ P, p)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → determinant (z i) (z j) ≠ 0)
    (L : ℝ) (hL : 0 ≤ L)
    (hexpand : ∀ j ∈ s,
      L * ((encodedBitEvent b e (rootWitnessEvent P S (z j) R)).card : ℝ) ≤
        (hammingNeighborhood r (encodedBitEvent b e (rootWitnessEvent P S (z j) R))).card) :
    L * ((encodedBitEvent b e (s.biUnion fun j => rootWitnessEvent P S (z j) R)).card : ℝ) ≤
      Fintype.card (P × Fin b → Bool) := by
  classical
  rw [encodedBitEvent_biUnion]
  apply separated_expansion_packing s _ r L hL _ hexpand
  intro i hi j hj hij a ha c hc
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hc
  have hxi := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
  have hyj := (Finset.mem_filter.mp (Finset.mem_product.mp hy).1).2
  exact encoded_box_lines_separated P hP S b m e x y (z i) (z j) R U (2 * r)
    hU hbound hlarge (hsep i hi j hj hij) hxi hyj

/-- Conditioning costs the reciprocal acceptance density. When growth beats
this cost, the all-class bound is nontrivial, with no factor counting lines. -/
theorem density_bound_after_balanced_encoding (q a L c : ℝ)
    (hq : 0 ≤ q) (hL : 0 < L) (ha : Real.exp (-c) ≤ a)
    (hpack : L * (q * a) ≤ 1) : q ≤ Real.exp c / L := by
  have hqa : L * q * Real.exp (-c) ≤ 1 := by
    calc
      _ ≤ L * q * a := mul_le_mul_of_nonneg_left ha (mul_nonneg hL.le hq)
      _ ≤ 1 := by simpa [mul_assoc] using hpack
  apply (le_div_iff₀ hL).mpr
  have hm := mul_le_mul_of_nonneg_right hqa (Real.exp_nonneg c)
  rw [mul_assoc (L * q), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
    one_mul] at hm
  simpa [mul_comm] using hm

/-- A cube packing estimate transfers back to the original uniform root law
with the explicit acceptance penalty exp(2*d*k/2^b). -/
theorem balanced_encoding_transfer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] (d b : ℕ)
    (hd : 0 < d) (hb : 2 * d ≤ 2 ^ b) (hK : ∀ i, Fintype.card (K i) = d)
    (e : ∀ i, K i × Fin (2 ^ b / d) ↪ (Fin b → Bool))
    (E : Finset (∀ i, K i)) (L : ℝ) (hL : 0 < L)
    (hpack : L * ((encodedBitEvent b e E).card : ℝ) ≤
      Fintype.card (ι × Fin b → Bool)) :
    (E.card : ℝ) / Fintype.card (∀ i, K i) ≤
      Real.exp (2 * (d : ℝ) / 2 ^ b * Fintype.card ι) / L := by
  have hKpos : 0 < Fintype.card (∀ i, K i) := by
    simp only [Fintype.card_pi, hK, Finset.prod_const, Finset.card_univ]
    exact pow_pos hd _
  have hN : 0 < (Fintype.card (ι → Fin b → Bool) : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    positivity
  have hcard : Fintype.card (ι × Fin b → Bool) =
      Fintype.card (ι → Fin b → Bool) := by
    simp [pow_mul, Nat.mul_comm]
  apply density_bound_after_balanced_encoding _
    (((encodedEvent e Finset.univ).card : ℝ) / Fintype.card (ι → Fin b → Bool))
    L _ (by positivity) hL
  · convert binary_acceptance_exp_lower d b hd hb hK e using 1
    congr 1
    ring
  · rw [← encodedEvent_ambient_fraction e hKpos, ← mul_div_assoc]
    apply (div_le_one hN).mpr
    simpa only [card_encodedBitEvent, hcard] using hpack

/-- Exponential expansion survives conditioning exactly when its rate exceeds
the explicit balancing cost. The packing/expansion premise remains visible. -/
theorem balanced_encoding_exponential_transfer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] (d b : ℕ)
    (hd : 0 < d) (hb : 2 * d ≤ 2 ^ b) (hK : ∀ i, Fintype.card (K i) = d)
    (e : ∀ i, K i × Fin (2 ^ b / d) ↪ (Fin b → Bool))
    (E : Finset (∀ i, K i)) (κ : ℝ)
    (hpack : Real.exp (κ * Fintype.card ι) * ((encodedBitEvent b e E).card : ℝ) ≤
      Fintype.card (ι × Fin b → Bool)) :
    (E.card : ℝ) / Fintype.card (∀ i, K i) ≤
      Real.exp (-(κ - 2 * (d : ℝ) / 2 ^ b) * Fintype.card ι) := by
  calc
    _ ≤ Real.exp (2 * (d : ℝ) / 2 ^ b * Fintype.card ι) /
        Real.exp (κ * Fintype.card ι) :=
      balanced_encoding_transfer d b hd hb hK e E _ (Real.exp_pos _) hpack
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

end BinaryFormMoat
