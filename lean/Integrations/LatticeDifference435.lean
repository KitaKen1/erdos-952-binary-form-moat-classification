import Integrations.WalkDisplacement435
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

namespace BinaryFormMoat.GeometryIntegration
open Module
open EntropyIntegration

def pointDifferences (E : Finset Point) : Finset Point :=
  (E ×ˢ E).image (fun xy => xy.1 - xy.2)

theorem mem_pointDifferences (E : Finset Point) (h : Point) :
    h ∈ pointDifferences E ↔ ∃ x ∈ E, ∃ y ∈ E, x - y = h := by
  simp only [pointDifferences, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩
    exact ⟨x, hx, y, hy, he⟩
  · rintro ⟨x, hx, y, hy, he⟩
    exact ⟨(x, y), ⟨hx, hy⟩, he⟩

theorem pointDifferences_card_le (E : Finset Point) :
    (pointDifferences E).card ≤ E.card ^ 2 := by
  exact Finset.card_image_le.trans_eq (by simp [Finset.card_product, pow_two])

def pointLattice (a b : Point) : Submodule ℤ Point :=
  Submodule.span ℤ (Set.range ![a, b])

theorem independent_pair_of_det_ne_zero (a b : Point)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) : LinearIndependent ℤ ![a, b] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  simp [Fin.sum_univ_two] at hx hy
  have hx0 : (a.1 * b.2 - a.2 * b.1) * c 0 = 0 := by
    calc
      _ = (c 0 * a.1 + c 1 * b.1) * b.2 -
          (c 0 * a.2 + c 1 * b.2) * b.1 := by ring
      _ = 0 := by rw [hx, hy]; ring
  have hx1 : (a.1 * b.2 - a.2 * b.1) * c 1 = 0 := by
    calc
      _ = (c 0 * a.2 + c 1 * b.2) * a.1 -
          (c 0 * a.1 + c 1 * b.1) * a.2 := by ring
      _ = 0 := by rw [hx, hy]; ring
  have hc0 := (mul_eq_zero.mp hx0).resolve_left hdet
  have hc1 := (mul_eq_zero.mp hx1).resolve_left hdet
  fin_cases i <;> assumption

/-- The determinant counts the quotient of the lattice actually generated
by a,b. A basis is constructed from nonzero determinant, not assumed. -/
theorem pointLattice_card (a b : Point)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) :
    Nat.card (Point ⧸ pointLattice a b) = (a.1 * b.2 - a.2 * b.1).natAbs := by
  let hli := independent_pair_of_det_ne_zero a b hdet
  have hv : (fun i => ((Basis.span hli) i : Point)) = ![a, b] := by
    funext i
    exact Basis.coe_span_apply hli i
  rw [← Submodule.natAbs_det_basis_change (Basis.finTwoProd ℤ)
    (pointLattice a b) (Basis.span hli)]
  change ((Basis.finTwoProd ℤ).det (fun i => ((Basis.span hli) i : Point))).natAbs = _
  rw [hv]
  simp [Basis.det_apply, Matrix.det_fin_two, Basis.toMatrix_apply,
    Basis.coe_finTwoProd_repr, mul_comm]

/-- A finite covering certificate bounds the quotient, without a volume
measure, primitivity, or a pre-existing finiteness instance for the quotient. -/
theorem quotient_card_le_of_box_cover (N : Submodule ℤ Point)
    (H : Finset Point) (B : ℕ)
    (hcover : ∀ k : Point, ∃ h ∈ H, ∃ e ∈ displacementBox B,
      N.mkQ (h + e) = N.mkQ k) :
    Nat.card (Point ⧸ N) ≤ H.card * (2 * B + 1) ^ 2 := by
  let f : ↥H × BoundedDisplacement B → Point ⧸ N := fun x => N.mkQ (x.1.1 + x.2.1)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := N.mkQ_surjective q
    obtain ⟨h, hh, e, he, hq⟩ := hcover k
    exact ⟨(⟨h, hh⟩, ⟨e, he⟩), hq⟩
  have h := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    displacementBox_card] using h

/-- The finite-counting end of many differences. Constructing hcover from
interpolated paths and Brouwer is deliberately not a premise hidden in a def. -/
theorem determinant_le_differences_of_cover (E : Finset Point) (a b : Point)
    (D : ℕ) (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0)
    (hcover : ∀ k : Point, ∃ h ∈ pointDifferences E,
      ∃ e ∈ displacementBox (2 * D),
        (pointLattice a b).mkQ (h + e) = (pointLattice a b).mkQ k) :
    (a.1 * b.2 - a.2 * b.1).natAbs ≤
      (pointDifferences E).card * (4 * D + 1) ^ 2 := by
  rw [← pointLattice_card a b hdet]
  convert quotient_card_le_of_box_cover (pointLattice a b) (pointDifferences E)
    (2 * D) hcover using 1
  ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.mem_pointDifferences
#print axioms BinaryFormMoat.GeometryIntegration.pointDifferences_card_le
#print axioms BinaryFormMoat.GeometryIntegration.independent_pair_of_det_ne_zero
#print axioms BinaryFormMoat.GeometryIntegration.pointLattice_card
#print axioms BinaryFormMoat.GeometryIntegration.quotient_card_le_of_box_cover
#print axioms BinaryFormMoat.GeometryIntegration.determinant_le_differences_of_cover
