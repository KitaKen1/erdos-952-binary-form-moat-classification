import Moat.BlockHamming
import Moat.BoxLineWitness
import Moat.DeterminantGeometry

namespace BinaryFormMoat

/-- The Hamming distance on batch coordinates agrees with the disagreement
count in the arithmetic determinant lemma. -/
theorem extend_disagreement_card (P : Finset ℕ) (ρ σ : (p : P) → ZMod p.val) :
    (P.filter fun p => extendRootAssignment P ρ p ≠ extendRootAssignment P σ p).card =
      hammingDist ρ σ := by
  classical
  rw [Finset.card_eq_sum_ones, hammingDist, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_coe_sort P]
  apply Finset.sum_congr rfl
  intro p _
  simp [extendRootAssignment, p.property]

/-- The determinant separation lemma in the same finite-coordinate interface
as the concentration and encoding results. -/
theorem rectangle_witnesses_collinear_hamming (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ρ σ : (p : P) → ZMod p.val)
    (z w : Point) (A B U h : ℕ) (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hamming : hammingDist ρ σ ≤ h)
    (hlarge : (2 * A * B) * U ^ h < ∏ p ∈ P, p)
    (hzx : z.1.natAbs ≤ A) (hzy : z.2.natAbs ≤ B)
    (hwx : w.1.natAbs ≤ A) (hwy : w.2.natAbs ≤ B)
    (hz : ∀ p : P, (z.1 : ZMod p.val) = ρ p * (z.2 : ZMod p.val))
    (hw : ∀ p : P, (w.1 : ZMod p.val) = σ p * (w.2 : ZMod p.val)) :
    determinant z w = 0 := by
  apply rectangle_witnesses_collinear P hP (extendRootAssignment P ρ)
    (extendRootAssignment P σ) z w A B U h hU hbound
  · rwa [extend_disagreement_card]
  · exact hlarge
  · exact hzx
  · exact hzy
  · exact hwx
  · exact hwy
  · intro p hp
    simpa [extendRootAssignment, hp] using hz ⟨p, hp⟩
  · intro p hp
    simpa [extendRootAssignment, hp] using hw ⟨p, hp⟩

theorem determinant_int_mul (a b : ℤ) (z w : Point) :
    determinant (a * z.1, a * z.2) (b * w.1, b * w.2) = a * b * determinant z w := by
  simp only [determinant]
  ring

/-- Two fixed lines with nearby witness assignments in a sufficiently small
box must be the same rational line. Integer multiplier choices cost nothing. -/
theorem box_line_witnesses_collinear (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ σ : (p : P) → ZMod p.val) (z w : Point) (R U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U) (hamming : hammingDist ρ σ ≤ h)
    (hlarge : (2 * R * R) * U ^ h < ∏ p ∈ P, p)
    (hz : BoxLineWitness P z R ρ) (hw : BoxLineWitness P w R σ) :
    determinant z w = 0 := by
  obtain ⟨a, ha, hRa, hza⟩ := hz
  obtain ⟨b, hb, hRb, hwb⟩ := hw
  have hdet := rectangle_witnesses_collinear_hamming P hP ρ σ
    (a * z.1, a * z.2) (b * w.1, b * w.2) R R U h hU hbound hamming hlarge
    ((le_max_left _ _).trans hRa) ((le_max_right _ _).trans hRa)
    ((le_max_left _ _).trans hRb) ((le_max_right _ _).trans hRb) hza hwb
  rw [determinant_int_mul] at hdet
  exact (mul_eq_zero.mp hdet).resolve_left (mul_ne_zero ha hb)

/-- Arithmetic separation survives arbitrary injective binary block codes.
Thus full-cube neighborhoods of different line classes can be packed. -/
theorem encoded_box_lines_separated (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (b m : ℕ)
    (e : ∀ p : P, (S p) × Fin m ↪ (Fin b → Bool))
    (x y : (∀ p : P, S p) × (P → Fin m)) (z w : Point) (R U h : ℕ)
    (hU : 1 ≤ U) (hbound : ∀ p ∈ P, p ≤ U)
    (hlarge : (2 * R * R) * U ^ h < ∏ p ∈ P, p) (hne : determinant z w ≠ 0)
    (hz : BoxLineWitness P z R (fun p => (x.1 p).val))
    (hw : BoxLineWitness P w R (fun p => (y.1 p).val)) :
    h < hammingDist (fun q : P × Fin b => blockEncoding e x q.1 q.2)
      (fun q : P × Fin b => blockEncoding e y q.1 q.2) := by
  by_contra hn
  apply hne
  apply box_line_witnesses_collinear P hP _ _ z w R U h hU hbound _ hlarge hz hw
  exact (hammingDist_comp_le_hammingDist (fun _ => Subtype.val)).trans
    ((root_hamming_le_bits b e x y).trans (Nat.le_of_not_gt hn))

end BinaryFormMoat
