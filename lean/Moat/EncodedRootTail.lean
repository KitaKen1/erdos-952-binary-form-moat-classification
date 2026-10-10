import Moat.EncodingDensity
import Moat.DyadicLineTail

namespace BinaryFormMoat

/-- Passing from a finite box to the dependent type of its entries preserves
every event count, not merely the one-coordinate marginals. -/
theorem subtype_box_event_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, DecidableEq (K i)] (S : ∀ i, Finset (K i))
    (Q : (∀ i, K i) → Prop) [DecidablePred Q] :
    ((Finset.univ.filter fun σ : ∀ i, S i => Q (fun i => (σ i).val)).card) =
      ((Fintype.piFinset S).filter Q).card := by
  classical
  apply Finset.card_bij (fun σ _ i => (σ i).val)
  · intro σ hσ
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => (σ i).property),
      (Finset.mem_filter.mp hσ).2⟩
  · intro σ _ τ _ h
    exact funext fun i => Subtype.ext (congrFun h i)
  · intro σ hσ
    obtain ⟨hS, hQ⟩ := Finset.mem_filter.mp hσ
    exact ⟨fun i => ⟨σ i, Fintype.mem_piFinset.mp hS i⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩, rfl⟩

/-- The complete root product is counted identically in the subtype and
finset presentations. -/
theorem subtype_box_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} (S : ∀ i, Finset (K i)) :
    Fintype.card (∀ i, S i) = (Fintype.piFinset S).card := by
  simp [Fintype.card_pi]

/-- An ambient density cannot exceed the corresponding conditional density,
because the event includes all auxiliary labels of its root assignments. -/
theorem encodedEvent_ambient_le {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] {K B : ι → Type*} [∀ i, Fintype (K i)] [∀ i, Fintype (B i)]
    (e : ∀ i, K i × A ↪ B i) (hK : 0 < Fintype.card (∀ i, K i))
    (E : Finset (∀ i, K i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hprob : (E.card : ℝ) / Fintype.card (∀ i, K i) ≤ ε) :
    ((encodedEvent e E).card : ℝ) / Fintype.card (∀ i, B i) ≤ ε := by
  rw [encodedEvent_ambient_fraction e hK E]
  have haccept : ((encodedEvent e Finset.univ).card : ℝ) /
      Fintype.card (∀ i, B i) ≤ 1 := by
    apply div_le_one_of_le₀
    · exact_mod_cast Finset.card_le_univ _
    · exact Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_right hprob (by positivity)).trans
    (mul_le_of_le_one_right hε haccept)

/-- A fixed-line event on the finite type of root choices. -/
noncomputable def rootWitnessEvent (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p))
    (z : Point) (R : ℕ) : Finset (∀ p : P, S p) := by
  classical
  exact Finset.univ.filter fun σ => BoxLineWitness P z R (fun p => (σ p).val)

/-- The checked fixed-line bound lifts to a binary cube with exactly the
same uniform-root probability estimate. No biased-root mean is substituted. -/
theorem encoded_irreducible_line_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (b m : ℕ) (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (R T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hgap : Real.log (R : ℝ) + Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (z : Point) (hz : IsCoprime z.1 z.2) :
    ((encodedEvent e (rootWitnessEvent P S z R)).card : ℝ) /
      Fintype.card (P → Fin b → Bool) ≤ Real.exp (-η ^ 2 * P.card / 2) := by
  classical
  have hK : 0 < Fintype.card (∀ p : P, S p) := by
    rw [subtype_box_card, Fintype.card_piFinset]
    exact Finset.prod_pos fun p _ => by rw [hcard p p.property]; omega
  apply encodedEvent_ambient_le e hK _ _ (Real.exp_nonneg _)
  rw [rootWitnessEvent, subtype_box_event_card (fun p : P => S p) (BoxLineWitness P z R),
    subtype_box_card]
  exact irreducible_dyadic_box_line_tail f hf hd P hP hne S hcard hroot
    R T hT hpT η hη hgap z hz

end BinaryFormMoat
