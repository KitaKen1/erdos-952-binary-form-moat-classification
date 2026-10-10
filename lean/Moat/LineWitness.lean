import Moat.RootConcentration

namespace BinaryFormMoat

/-- Extend a batch assignment by zero away from its prime batch. Values off
the batch have no mathematical role; this only connects two finite interfaces. -/
noncomputable def extendRootAssignment (P : Finset ℕ) (σ : (p : P) → ZMod p.val)
    (p : ℕ) : ZMod p := if hp : p ∈ P then σ ⟨p, hp⟩ else 0

/-- A witness multiplier must contain every missed prime. Taking logarithms
forces a lower bound on the logarithmic root-hit cost. -/
theorem line_witness_log_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ : (p : ℕ) → ZMod p) (z : Point) (a : ℤ) (ha : a ≠ 0)
    (hhit : ∀ p ∈ P, ((a * z.1 : ℤ) : ZMod p) = ρ p * ((a * z.2 : ℤ) : ZMod p)) :
    (∑ p ∈ P, Real.log (p : ℝ)) - Real.log (a.natAbs : ℝ) ≤
      ∑ p ∈ P, if (z.1 : ZMod p) = ρ p * (z.2 : ZMod p) then Real.log (p : ℝ) else 0 := by
  classical
  have hmiss : (∑ p ∈ P.filter (fun p => (z.1 : ZMod p) ≠ ρ p * (z.2 : ZMod p)),
      Real.log (p : ℝ)) ≤ Real.log (a.natAbs : ℝ) := by
    apply log_prime_product_le _ (fun p hp => hP p (Finset.mem_filter.mp hp).1) a ha
    intro p hp
    obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
    let : Fact p.Prime := ⟨hP p hp⟩
    exact multiplier_dvd_of_slope_miss p (ρ p) z.1 z.2 a hne (hhit p hp)
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p => (z.1 : ZMod p) = ρ p * (z.2 : ZMod p)) (fun p => Real.log (p : ℝ))
  rw [← Finset.sum_filter]
  linarith

/-- A fixed-line witness is a nonzero integer multiple, with an explicit cap
on that multiplier, satisfying all the chosen root-line constraints. -/
def BoundedLineWitness (P : Finset ℕ) (z : Point) (L : ℕ)
    (σ : (p : P) → ZMod p.val) : Prop :=
  ∃ a : ℤ, a ≠ 0 ∧ a.natAbs ≤ L ∧ ∀ p : P,
    ((a * z.1 : ℤ) : ZMod p.val) = σ p * ((a * z.2 : ℤ) : ZMod p.val)

/-- The finite set of root assignments having a witness on a fixed line. -/
noncomputable def lineWitnessAssignments (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p))
    (z : Point) (L : ℕ) : Finset ((p : P) → ZMod p.val) := by
  classical
  exact (Fintype.piFinset (fun p : P => S p)).filter (BoundedLineWitness P z L)

/-- All bounded witnesses on one line lie in a single high-cost event; there
is no union bound over the possible multipliers. -/
theorem bounded_line_witness_cost (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : Point) (L : ℕ) (σ : (p : P) → ZMod p.val) (hσ : BoundedLineWitness P z L σ) :
    (∑ p ∈ P, Real.log (p : ℝ)) - Real.log (L : ℝ) ≤ rootLogCost P z σ := by
  classical
  obtain ⟨a, ha, hL, hhit⟩ := hσ
  have hlog : Real.log (a.natAbs : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr ha) (by exact_mod_cast hL)
  have hlower := line_witness_log_lower P hP (extendRootAssignment P σ) z a ha
    (fun p hp => by simpa [extendRootAssignment, hp] using hhit ⟨p, hp⟩)
  have hcost : (∑ p ∈ P, if (z.1 : ZMod p) = extendRootAssignment P σ p * (z.2 : ZMod p)
      then Real.log (p : ℝ) else 0) = rootLogCost P z σ := by
    rw [rootLogCost, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro p _
    simp [extendRootAssignment, p.property]
  rw [hcost] at hlower
  linarith

/-- Exponential probability bound for the existence of any bounded witness on
one fixed primitive line. It retains the coefficient loss and an explicit gap
between the total prime log mass and the allowed witness size. -/
theorem fixed_line_witness_upper_tail (f : Polynomial ℤ) (d : ℕ)
    (hdeg : f.natDegree ≤ d) (hd : 0 < d)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize d) z ≠ 0)
    (A : ℕ) (hA : 0 < A) (hza : z.1.natAbs ≤ A) (hzb : z.2.natAbs ≤ A)
    (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : Real.log (A : ℝ) + Real.log (coefficientBound f d : ℝ) / d + t ≤
      (∑ p ∈ P, Real.log (p : ℝ)) - Real.log (L : ℝ)) :
    ((lineWitnessAssignments P S z L).card : ℝ) /
      (Fintype.piFinset (fun p : P => S p)).card ≤
      Real.exp (-2 * t ^ 2 / (∑ p ∈ P, (Real.log (p : ℝ)) ^ 2)) := by
  classical
  apply le_trans _ (root_log_cost_upper_tail f d hdeg hd P hP S hcard hroot z hprim hz
    A hA hza hzb t ht)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro σ hσ
  obtain ⟨hmem, hwit⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨hmem, hgap.trans (bounded_line_witness_cost P hP z L σ hwit)⟩

end BinaryFormMoat
