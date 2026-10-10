import Moat.RectanglePacking

namespace BinaryFormMoat

/-- Separation needs a determinant bound, independently of any coordinate box. -/
theorem witnesses_collinear_of_determinant_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ρ σ : (p : P) → ZMod p.val)
    (z w : Point) (M U h : ℕ) (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hamming : hammingDist ρ σ ≤ h)
    (hlarge : M * U ^ h < ∏ p ∈ P, p) (hdet : (determinant z w).natAbs ≤ M)
    (hz : ∀ p : P, (z.1 : ZMod p.val) = ρ p * (z.2 : ZMod p.val))
    (hw : ∀ p : P, (w.1 : ZMod p.val) = σ p * (w.2 : ZMod p.val)) :
    determinant z w = 0 := by
  classical
  let ρ' := extendRootAssignment P ρ
  let σ' := extendRootAssignment P σ
  have hcommon : M < ∏ p ∈ P.filter (fun p => ρ' p = σ' p), p :=
    agreement_product_large P ρ' σ' U h M hU hbound
      (by simpa only [ρ', σ', extend_disagreement_card] using hamming) hlarge
  apply determinant_zero_of_common_primes (P.filter (fun p => ρ' p = σ' p))
    (fun p hp => hP p (Finset.mem_filter.mp hp).1) ρ' z w
  · intro p hp
    simpa [ρ', extendRootAssignment, (Finset.mem_filter.mp hp).1] using
      hz ⟨p, (Finset.mem_filter.mp hp).1⟩
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    rw [he]
    simpa [σ', extendRootAssignment, hp] using hw ⟨p, hp⟩
  · exact hdet.trans_lt hcommon

def FiniteSetLineWitness (E : Finset Point) (P : Finset ℕ) (z : Point)
    (σ : (p : P) → ZMod p.val) : Prop :=
  ∃ a : ℤ, a ≠ 0 ∧ (a * z.1, a * z.2) ∈ E ∧
    ∀ p : P, ((a * z.1 : ℤ) : ZMod p.val) =
      σ p * ((a * z.2 : ℤ) : ZMod p.val)

theorem finiteSet_line_witness_box (E : Finset Point) (P : Finset ℕ) (z : Point)
    (R : ℕ) (hradius : ∀ w ∈ E, max w.1.natAbs w.2.natAbs ≤ R)
    (σ : (p : P) → ZMod p.val) (h : FiniteSetLineWitness E P z σ) :
    BoxLineWitness P z R σ := by
  obtain ⟨a, ha, hE, hhit⟩ := h
  exact ⟨a, ha, hradius _ hE, hhit⟩

noncomputable def finiteSetRootWitnessEvent (E : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (z : Point) : Finset (∀ p : P, S p) := by
  classical
  exact Finset.univ.filter fun σ => FiniteSetLineWitness E P z (fun p => (σ p).val)

theorem finiteSet_root_event_subset_box (E : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (z : Point) (R : ℕ)
    (hradius : ∀ w ∈ E, max w.1.natAbs w.2.natAbs ≤ R) :
    finiteSetRootWitnessEvent E P S z ⊆ rootWitnessEvent P S z R := by
  classical
  intro σ hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    finiteSet_line_witness_box E P z R hradius _ (Finset.mem_filter.mp hσ).2⟩

theorem encoded_finiteSet_irreducible_line_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (E : Finset Point) (R : ℕ)
    (hradius : ∀ w ∈ E, max w.1.natAbs w.2.natAbs ≤ R)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (b m : ℕ) (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hgap : Real.log (R : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (z : Point) (hz : IsCoprime z.1 z.2) :
    ((encodedBitEvent b e (finiteSetRootWitnessEvent E P S z)).card : ℝ) /
      Fintype.card (P × Fin b → Bool) ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  have hcount : (encodedEvent e (finiteSetRootWitnessEvent E P S z)).card ≤
      (encodedEvent e (rootWitnessEvent P S z R)).card := by
    apply Finset.card_le_card
    exact Finset.map_subset_map.mpr (Finset.product_subset_product_left
      (finiteSet_root_event_subset_box E P S z R hradius))
  have hden : Fintype.card (P × Fin b → Bool) = Fintype.card (P → Fin b → Bool) := by
    simp [pow_mul, Nat.mul_comm]
  rw [card_encodedBitEvent, hden]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)).trans
    (encoded_irreducible_line_tail f hf hd P hP hne S hcard hroot b m e
      R T hT hpT η hη hgap z hz)

theorem finiteSet_line_witnesses_collinear (E : Finset Point) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ρ σ : (p : P) → ZMod p.val) (z w : Point)
    (M U h : ℕ) (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hamming : hammingDist ρ σ ≤ h) (hlarge : M * U ^ h < ∏ p ∈ P, p)
    (hdet : ∀ x ∈ E, ∀ y ∈ E, (determinant x y).natAbs ≤ M)
    (hz : FiniteSetLineWitness E P z ρ) (hw : FiniteSetLineWitness E P w σ) :
    determinant z w = 0 := by
  obtain ⟨a, ha, hEa, hza⟩ := hz
  obtain ⟨b, hb, hEb, hwb⟩ := hw
  have hzero := witnesses_collinear_of_determinant_bound P hP ρ σ
    (a * z.1, a * z.2) (b * w.1, b * w.2) M U h hU hbound hamming hlarge
    (hdet _ hEa _ hEb) hza hwb
  rw [determinant_int_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero ha hb)

theorem encoded_finiteSet_lines_separated (E : Finset Point) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (x y : (∀ p : P, S p) × (P → Fin m)) (z w : Point) (M U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : M * U ^ h < ∏ p ∈ P, p)
    (hdet : ∀ v ∈ E, ∀ v' ∈ E, (determinant v v').natAbs ≤ M)
    (hne : determinant z w ≠ 0)
    (hz : FiniteSetLineWitness E P z (fun p => (x.1 p).val))
    (hw : FiniteSetLineWitness E P w (fun p => (y.1 p).val)) :
    h < hammingDist (bitEncoding b e x) (bitEncoding b e y) := by
  by_contra hn
  apply hne
  apply finiteSet_line_witnesses_collinear E P hP _ _ z w M U h
    hU hbound _ hlarge hdet hz hw
  exact (hammingDist_comp_le_hammingDist (fun _ => Subtype.val)).trans
    ((root_hamming_le_bits b e x y).trans (Nat.le_of_not_gt hn))

noncomputable def finiteSetWitnessEvent (E : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) : Finset (∀ p : P, S p) := by
  classical
  exact Finset.univ.filter fun σ => ∃ z ∈ E, z ≠ (0, 0) ∧
    ∀ p : P, (z.1 : ZMod p.val) = (σ p).val * (z.2 : ZMod p.val)

theorem finiteSetWitnessEvent_eq_biUnion (E : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (s : Finset Point)
    (hprim : ∀ w ∈ s, IsCoprime w.1 w.2)
    (hcover : ∀ z ∈ E, z ≠ (0, 0) →
      ∃ w ∈ s, ∃ a : ℤ, a ≠ 0 ∧ z = (a * w.1, a * w.2)) :
    finiteSetWitnessEvent E P S = s.biUnion fun z => finiteSetRootWitnessEvent E P S z := by
  classical
  ext σ
  constructor
  · intro hσ
    obtain ⟨z, hz, hne, hhit⟩ := (Finset.mem_filter.mp hσ).2
    obtain ⟨w, hw, a, ha, he⟩ := hcover z hz hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, a, ha, by simpa only [he] using hz,
        by simpa only [he] using hhit⟩⟩
  · intro hσ
    obtain ⟨w, hw, hσ⟩ := Finset.mem_biUnion.mp hσ
    obtain ⟨a, ha, hE, hhit⟩ := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (a * w.1, a * w.2), hE, ?_, hhit⟩
    intro he
    have hfirst : a * w.1 = 0 := congrArg Prod.fst he
    have hsecond : a * w.2 = 0 := congrArg Prod.snd he
    obtain h | h := (hprim w hw).ne_zero_or_ne_zero
    · exact mul_ne_zero ha h hfirst
    · exact mul_ne_zero ha h hsecond

/-- A coordinate radius supplies the line cover and tails; a separate bound
on determinants supplies packing. No axis alignment is required of E. -/
theorem encoded_finiteSet_packing (E : Finset Point) (R M : ℕ)
    (hradius : ∀ w ∈ E, max w.1.natAbs w.2.natAbs ≤ R)
    (hdet : ∀ z ∈ E, ∀ w ∈ E, (determinant z w).natAbs ≤ M)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool)) (U r : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : M * U ^ (2 * r) < ∏ p ∈ P, p) (L : ℝ) (hL : 0 ≤ L)
    (hexpand : ∀ z, IsCoprime z.1 z.2 →
      L * ((encodedBitEvent b e (finiteSetRootWitnessEvent E P S z)).card : ℝ) ≤
        (hammingNeighborhood r (encodedBitEvent b e (finiteSetRootWitnessEvent E P S z))).card) :
    L * ((encodedBitEvent b e (finiteSetWitnessEvent E P S)).card : ℝ) ≤
      Fintype.card (P × Fin b → Bool) := by
  classical
  obtain ⟨s, hprim, hsep, hcover⟩ := exists_rectangle_line_representatives R R
  have hcoverE : ∀ z ∈ E, z ≠ (0, 0) →
      ∃ w ∈ s, ∃ a : ℤ, a ≠ 0 ∧ z = (a * w.1, a * w.2) := by
    intro z hz hzero
    apply hcover z _ hzero
    exact (mem_rectanglePoints z R R).mpr (max_le_iff.mp (hradius z hz))
  rw [finiteSetWitnessEvent_eq_biUnion E P S s (fun z hz => (hprim z hz).1) hcoverE,
    encodedBitEvent_biUnion]
  apply separated_expansion_packing s _ r L hL _ (fun z hz => hexpand z (hprim z hz).1)
  intro z hz w hw hne x hx y hy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
  have hxhit := (Finset.mem_filter.mp (Finset.mem_product.mp hx').1).2
  have hyhit := (Finset.mem_filter.mp (Finset.mem_product.mp hy').1).2
  exact encoded_finiteSet_lines_separated E P hP S b m e x' y' z w M U (2 * r)
    hU hbound hlarge hdet (hsep z hz w hw hne) hxhit hyhit

/-- Finite counting extracts one root choice avoiding the whole finite set. -/
theorem exists_finiteSet_avoiding_root_assignment (E : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (hS : ∀ p : P, (S p).Nonempty)
    (htail : ((finiteSetWitnessEvent E P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) < 1) :
    ∃ σ : (∀ p : P, S p), ∀ z ∈ E, z ≠ (0, 0) →
      ∃ p : P, (z.1 : ZMod p.val) ≠ (σ p).val * (z.2 : ZMod p.val) := by
  classical
  have hchoices : Nonempty (∀ p : P, S p) := ⟨fun p =>
    ⟨Classical.choose (hS p), Classical.choose_spec (hS p)⟩⟩
  have hpos : (0 : ℝ) < Fintype.card (∀ p : P, S p) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hchoices
  have hlt : (finiteSetWitnessEvent E P S).card <
      (Finset.univ : Finset (∀ p : P, S p)).card := by
    rw [Finset.card_univ]
    exact_mod_cast (div_lt_one hpos).mp htail
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, fun z hz hzero => ?_⟩
  by_contra h
  apply hσ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, z, hz, hzero, fun p => ?_⟩
  by_contra hp
  exact h ⟨p, hp⟩

end BinaryFormMoat
