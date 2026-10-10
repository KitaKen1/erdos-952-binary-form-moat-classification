import Integrations.AreaEnvelope435
import Integrations.FiniteSetHarper435
import Integrations.RootResidues435
import Moat.UniformSampling

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration HarperIntegration MeasureTheory ProbabilityTheory

/-- The actual additive residue tuple, indexed by distinct rational primes. -/
def residueTuple (P : Finset ℕ) (ρ : (p : P) → ZMod p.val) :
    Point →+ ((p : P) → ZMod p.val) where
  toFun z p := rootResidueHom p.val (ρ p) z
  map_zero' := by ext p; exact map_zero _
  map_add' a b := by ext p; exact map_add _ a b

theorem residueTuple_injOn_iff (H : Finset Point) (P : Finset ℕ)
    (ρ : (p : P) → ZMod p.val) :
    Set.InjOn (residueTuple P ρ) (H : Set Point) ↔
      ∀ z ∈ pointDifferences H, z ≠ 0 → ∃ p : P, rootResidueHom p.val (ρ p) z ≠ 0 := by
  constructor
  · intro hinj z hz hne
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_pointDifferences H z).mp hz
    by_contra h
    push Not at h
    have he : residueTuple P ρ a = residueTuple P ρ b := by
      ext p
      change rootResidueHom p.val (ρ p) a = rootResidueHom p.val (ρ p) b
      exact sub_eq_zero.mp (by simpa only [map_sub] using h p)
    exact hne (sub_eq_zero.mpr (hinj ha hb he))
  · intro h a ha b hb he
    by_contra hne
    obtain ⟨p, hp⟩ := h (a - b)
      ((mem_pointDifferences H _).mpr ⟨a, ha, b, hb, rfl⟩) (sub_ne_zero.mpr hne)
    apply hp
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun he p)

def nonInjectiveRootAssignments (H : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) : Finset (∀ p : P, S p) :=
  Finset.univ.filter (fun σ => ¬ Set.InjOn (residueTuple P (fun p => (σ p).val))
    (H : Set Point))

/-- A collision on H is exactly a nonzero kernel witness in H-H. -/
theorem nonInjectiveRootAssignments_eq (H : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) :
    nonInjectiveRootAssignments H P S = finiteSetWitnessEvent (pointDifferences H) P S := by
  classical
  ext σ
  simp only [nonInjectiveRootAssignments, finiteSetWitnessEvent, Finset.mem_filter,
    Finset.mem_univ, true_and, residueTuple_injOn_iff]
  push Not
  simp only [rootResidueHom_eq_zero_iff]
  rfl

theorem nonInjectiveRootAssignments_probability (H : Finset Point) (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p))
    [MeasurableSpace (∀ p : P, S p)] [MeasurableSingletonClass (∀ p : P, S p)] :
    (uniformOn (Set.univ : Set (∀ p : P, S p))).real
      {σ | ¬ Set.InjOn (residueTuple P (fun p => (σ p).val)) (H : Set Point)} =
      ((nonInjectiveRootAssignments H P S).card : ℝ) / Fintype.card (∀ p : P, S p) := by
  classical
  simpa only [Finset.coe_univ, Finset.card_univ, nonInjectiveRootAssignments] using
    (uniformOn_real_event (Finset.univ : Finset (∀ p : P, S p))
      (fun σ => ¬ Set.InjOn (residueTuple P (fun p => (σ p).val)) (H : Set Point)))

/-- Geometric separation for the actual walk difference set. Its radius and
determinant inputs are constructed; only the scalar batch conditions remain. -/
theorem walk_difference_separation_exp_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hgap : Real.log (max 1 (4 * (D * N)) : ℕ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : (16 * prefixArea z N) * (2 * T) ^ (2 * l) < ∏ p ∈ P, p) :
    let b := 16 * f.natDegree * q ^ 2 + 4
    ((nonInjectiveRootAssignments (pointDifferences (walkVertexSet z N)) P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) ≤ Real.exp (-(l : ℝ) / (4 * (b * q : ℕ))) := by
  rw [nonInjectiveRootAssignments_eq]
  apply harper_finiteSet_exp_tail f hf hd _ (max 1 (4 * (D * N))) (16 * prefixArea z N)
    _ (prefix_second_difference_determinant_le z N) P hP S hcard hroot q l hq hl hcount
    T hT hpT η hη hschedule hgap hlarge
  intro v hv
  exact (prefix_second_difference_radius_le z D N hstep v hv).trans (le_max_right _ _)

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.residueTuple_injOn_iff
#print axioms BinaryFormMoat.GeometryIntegration.nonInjectiveRootAssignments_eq
#print axioms BinaryFormMoat.GeometryIntegration.nonInjectiveRootAssignments_probability
#print axioms BinaryFormMoat.GeometryIntegration.walk_difference_separation_exp_tail
