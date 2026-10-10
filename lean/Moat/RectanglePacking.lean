import Moat.LineRepresentatives
import Moat.EncodedPacking

namespace BinaryFormMoat

/-- A witness keeps the two rectangle bounds separate, preserving the area
factor in arithmetic separation. -/
def RectangleLineWitness (P : Finset ℕ) (z : Point) (A B : ℕ)
    (σ : (p : P) → ZMod p.val) : Prop :=
  ∃ a : ℤ, a ≠ 0 ∧ (a * z.1).natAbs ≤ A ∧ (a * z.2).natAbs ≤ B ∧
    ∀ p : P, ((a * z.1 : ℤ) : ZMod p.val) =
      σ p * ((a * z.2 : ℤ) : ZMod p.val)

theorem rectangle_line_witness_box (P : Finset ℕ) (z : Point) (A B : ℕ)
    (σ : (p : P) → ZMod p.val) (h : RectangleLineWitness P z A B σ) :
    BoxLineWitness P z (max A B) σ := by
  obtain ⟨a, ha, hx, hy, hhit⟩ := h
  exact ⟨a, ha, max_le (hx.trans (le_max_left _ _)) (hy.trans (le_max_right _ _)), hhit⟩

noncomputable def rectangleRootWitnessEvent (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (z : Point) (A B : ℕ) :
    Finset (∀ p : P, S p) := by
  classical
  exact Finset.univ.filter fun σ => RectangleLineWitness P z A B (fun p => (σ p).val)

theorem rectangle_root_event_subset_box (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (z : Point) (A B : ℕ) :
    rectangleRootWitnessEvent P S z A B ⊆ rootWitnessEvent P S z (max A B) := by
  classical
  intro σ hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    rectangle_line_witness_box P z A B _ (Finset.mem_filter.mp hσ).2⟩

/-- The fixed-line tail applies to a rectangle via its sup-norm radius;
the determinant estimate below still uses its actual area. -/
theorem encoded_rectangle_irreducible_line_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (b m : ℕ) (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (A B T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hgap : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (z : Point) (hz : IsCoprime z.1 z.2) :
    ((encodedBitEvent b e (rectangleRootWitnessEvent P S z A B)).card : ℝ) /
      Fintype.card (P × Fin b → Bool) ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  have hcount : (encodedEvent e (rectangleRootWitnessEvent P S z A B)).card ≤
      (encodedEvent e (rootWitnessEvent P S z (max A B))).card := by
    apply Finset.card_le_card
    exact Finset.map_subset_map.mpr (Finset.product_subset_product_left
      (rectangle_root_event_subset_box P S z A B))
  have hden : Fintype.card (P × Fin b → Bool) = Fintype.card (P → Fin b → Bool) := by
    simp [pow_mul, Nat.mul_comm]
  rw [card_encodedBitEvent, hden]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)).trans
    (encoded_irreducible_line_tail f hf hd P hP hne S hcard hroot b m e
      (max A B) T hT hpT η hη hgap z hz)

theorem rectangle_line_witnesses_collinear (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ σ : (p : P) → ZMod p.val) (z w : Point) (A B U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U) (hamming : hammingDist ρ σ ≤ h)
    (hlarge : (2 * A * B) * U ^ h < ∏ p ∈ P, p)
    (hz : RectangleLineWitness P z A B ρ) (hw : RectangleLineWitness P w A B σ) :
    determinant z w = 0 := by
  obtain ⟨a, ha, hax, hay, hza⟩ := hz
  obtain ⟨b, hb, hbx, hby, hwb⟩ := hw
  have hdet := rectangle_witnesses_collinear_hamming P hP ρ σ
    (a * z.1, a * z.2) (b * w.1, b * w.2) A B U h hU hbound hamming hlarge
    hax hay hbx hby hza hwb
  rw [determinant_int_mul] at hdet
  exact (mul_eq_zero.mp hdet).resolve_left (mul_ne_zero ha hb)

theorem encoded_rectangle_lines_separated (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (x y : (∀ p : P, S p) × (P → Fin m)) (z w : Point) (A B U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : (2 * A * B) * U ^ h < ∏ p ∈ P, p) (hne : determinant z w ≠ 0)
    (hz : RectangleLineWitness P z A B (fun p => (x.1 p).val))
    (hw : RectangleLineWitness P w A B (fun p => (y.1 p).val)) :
    h < hammingDist (bitEncoding b e x) (bitEncoding b e y) := by
  by_contra hn
  apply hne
  apply rectangle_line_witnesses_collinear P hP _ _ z w A B U h hU hbound _ hlarge hz hw
  exact (hammingDist_comp_le_hammingDist (fun _ => Subtype.val)).trans
    ((root_hamming_le_bits b e x y).trans (Nat.le_of_not_gt hn))

/-- The event quantifies over all nonzero integer points, including points
with nontrivial gcd. No primitivity restriction is imposed on the witnesses. -/
noncomputable def rectangleWitnessEvent (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (A B : ℕ) : Finset (∀ p : P, S p) := by
  classical
  exact Finset.univ.filter fun σ => ∃ z ∈ rectanglePoints A B, z ≠ (0, 0) ∧
    ∀ p : P, (z.1 : ZMod p.val) = (σ p).val * (z.2 : ZMod p.val)

theorem rectangleWitnessEvent_eq_biUnion (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (A B : ℕ) (s : Finset Point)
    (hprim : ∀ w ∈ s, IsCoprime w.1 w.2)
    (hcover : ∀ z ∈ rectanglePoints A B, z ≠ (0, 0) →
      ∃ w ∈ s, ∃ a : ℤ, a ≠ 0 ∧ z = (a * w.1, a * w.2)) :
    rectangleWitnessEvent P S A B = s.biUnion fun z => rectangleRootWitnessEvent P S z A B := by
  classical
  ext σ
  constructor
  · intro hσ
    obtain ⟨z, hz, hne, hhit⟩ := (Finset.mem_filter.mp hσ).2
    obtain ⟨w, hw, a, ha, he⟩ := hcover z hz hne
    obtain ⟨hx, hy⟩ := (mem_rectanglePoints z A B).mp hz
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, ?_, ?_, ?_⟩⟩
    · simpa only [he] using hx
    · simpa only [he] using hy
    · simpa only [he] using hhit
  · intro hσ
    obtain ⟨w, hw, hσ⟩ := Finset.mem_biUnion.mp hσ
    obtain ⟨a, ha, hx, hy, hhit⟩ := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (a * w.1, a * w.2),
      (mem_rectanglePoints _ A B).mpr ⟨hx, hy⟩, ?_, hhit⟩
    intro he
    have hfirst : a * w.1 = 0 := congrArg Prod.fst he
    have hsecond : a * w.2 = 0 := congrArg Prod.snd he
    obtain h | h := (hprim w hw).ne_zero_or_ne_zero
    · exact mul_ne_zero ha h hfirst
    · exact mul_ne_zero ha h hsecond

/-- Arithmetic separation and a uniform expansion factor control the entire
rectangle event, with no factor counting the finite line representatives. -/
theorem encoded_rectangle_packing (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool)) (A B U r : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : (2 * A * B) * U ^ (2 * r) < ∏ p ∈ P, p)
    (L : ℝ) (hL : 0 ≤ L)
    (hexpand : ∀ z, IsCoprime z.1 z.2 →
      L * ((encodedBitEvent b e (rectangleRootWitnessEvent P S z A B)).card : ℝ) ≤
        (hammingNeighborhood r (encodedBitEvent b e (rectangleRootWitnessEvent P S z A B))).card) :
    L * ((encodedBitEvent b e (rectangleWitnessEvent P S A B)).card : ℝ) ≤
      Fintype.card (P × Fin b → Bool) := by
  classical
  obtain ⟨s, hprim, hsep, hcover⟩ := exists_rectangle_line_representatives A B
  rw [rectangleWitnessEvent_eq_biUnion P S A B s (fun z hz => (hprim z hz).1) hcover,
    encodedBitEvent_biUnion]
  apply separated_expansion_packing s _ r L hL _ (fun z hz => hexpand z (hprim z hz).1)
  intro z hz w hw hne x hx y hy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
  have hxhit := (Finset.mem_filter.mp (Finset.mem_product.mp hx').1).2
  have hyhit := (Finset.mem_filter.mp (Finset.mem_product.mp hy').1).2
  exact encoded_rectangle_lines_separated P hP S b m e x' y' z w A B U (2 * r)
    hU hbound hlarge (hsep z hz w hw hne) hxhit hyhit

end BinaryFormMoat
