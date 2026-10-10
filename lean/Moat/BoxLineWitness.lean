import Moat.LineWitness

namespace BinaryFormMoat

/-- The integral sup-norm radius of a lattice vector. -/
def pointRadius (z : Point) : ℕ := max z.1.natAbs z.2.natAbs

theorem pointRadius_pos_of_primitive (z : Point) (hz : IsCoprime z.1 z.2) :
    0 < pointRadius z := by
  obtain h | h := hz.ne_zero_or_ne_zero
  · exact (Int.natAbs_pos.mpr h).trans_le (le_max_left _ _)
  · exact (Int.natAbs_pos.mpr h).trans_le (le_max_right _ _)

/-- Scalar multiplication scales the integral radius exactly. -/
theorem pointRadius_int_mul (a : ℤ) (z : Point) :
    pointRadius (a * z.1, a * z.2) = a.natAbs * pointRadius z := by
  simp only [pointRadius, Int.natAbs_mul]
  exact (mul_max _ _ _).symm

/-- A nonzero integer multiple on the fixed line, in a prescribed box, that
satisfies every chosen prime constraint. -/
def BoxLineWitness (P : Finset ℕ) (z : Point) (R : ℕ)
    (σ : (p : P) → ZMod p.val) : Prop :=
  ∃ a : ℤ, a ≠ 0 ∧ pointRadius (a * z.1, a * z.2) ≤ R ∧ ∀ p : P,
    ((a * z.1 : ℤ) : ZMod p.val) = σ p * ((a * z.2 : ℤ) : ZMod p.val)

noncomputable def boxLineWitnessAssignments (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (z : Point) (R : ℕ) :
    Finset ((p : P) → ZMod p.val) := by
  classical
  exact (Fintype.piFinset (fun p : P => S p)).filter (BoxLineWitness P z R)

/-- The fixed direction's radius appears with a positive sign in the witness
cost. It will cancel its contribution to the mean, uniformly over directions. -/
theorem box_line_witness_cost (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : Point) (hz : 0 < pointRadius z) (R : ℕ)
    (σ : (p : P) → ZMod p.val) (hσ : BoxLineWitness P z R σ) :
    (∑ p ∈ P, Real.log (p : ℝ)) + Real.log (pointRadius z : ℝ) - Real.log (R : ℝ) ≤
      rootLogCost P z σ := by
  obtain ⟨a, ha, hR, hhit⟩ := hσ
  have hcost := bounded_line_witness_cost P hP z a.natAbs σ ⟨a, ha, le_rfl, hhit⟩
  rw [pointRadius_int_mul] at hR
  have ha' : 0 < (a.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr ha
  have hz' : 0 < (pointRadius z : ℝ) := by exact_mod_cast hz
  have hlog : Real.log ((a.natAbs : ℝ) * (pointRadius z : ℝ)) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (mul_pos ha' hz') (by exact_mod_cast hR)
  rw [Real.log_mul ha'.ne' hz'.ne'] at hlog
  linarith

/-- Uniform fixed-line bound inside a box. The gap assumption depends on the
form, box, and prime batch, but not on the direction z. This is still a bound
for each fixed line, not for the union of all lines. -/
theorem box_fixed_line_upper_tail (f : Polynomial ℤ) (d : ℕ)
    (hdeg : f.natDegree ≤ d) (hd : 0 < d)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize d) z ≠ 0)
    (R : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : Real.log (R : ℝ) + Real.log (coefficientBound f d : ℝ) / d + t ≤
      ∑ p ∈ P, Real.log (p : ℝ)) :
    ((boxLineWitnessAssignments P S z R).card : ℝ) /
      (Fintype.piFinset (fun p : P => S p)).card ≤
      Real.exp (-2 * t ^ 2 / (∑ p ∈ P, (Real.log (p : ℝ)) ^ 2)) := by
  classical
  have hv := pointRadius_pos_of_primitive z hprim
  apply le_trans _ (root_log_cost_upper_tail f d hdeg hd P hP S hcard hroot z hprim hz
    (pointRadius z) hv (le_max_left _ _) (le_max_right _ _) t ht)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro σ hσ
  obtain ⟨hmem, hwit⟩ := Finset.mem_filter.mp hσ
  refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
  have hc := box_line_witness_cost P hP z hv R σ hwit
  linarith

end BinaryFormMoat
