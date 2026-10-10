import Moat.Concentration
import Moat.LogBudget
import Mathlib.MeasureTheory.MeasurableSpace.Instances

namespace BinaryFormMoat

/-- The logarithmic hit cost for one assignment of roots over a prime batch. -/
noncomputable def rootLogCost (P : Finset ℕ) (z : Point) (σ : (p : P) → ZMod p.val) : ℝ :=
  ∑ p : P, if (z.1 : ZMod p.val) = σ p * (z.2 : ZMod p.val)
    then Real.log (p.val : ℝ) else 0

/-- Exponentially small upper tail for the fixed-direction logarithmic hit
cost. The coefficient loss in the mean remains visible in the threshold. -/
theorem root_log_cost_upper_tail (f : Polynomial ℤ) (d : ℕ)
    (hdeg : f.natDegree ≤ d) (hd : 0 < d)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (S : (p : ℕ) → Finset (ZMod p))
    (hcard : ∀ p ∈ P, (S p).card = d)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : Point) (hprim : IsCoprime z.1 z.2) (hz : value (f.homogenize d) z ≠ 0)
    (A : ℕ) (hA : 0 < A) (hza : z.1.natAbs ≤ A) (hzb : z.2.natAbs ≤ A)
    (t : ℝ) (ht : 0 ≤ t) :
    (((Fintype.piFinset (fun p : P => S p)).filter (fun σ =>
      Real.log (A : ℝ) + Real.log (coefficientBound f d : ℝ) / d + t ≤
        rootLogCost P z σ)).card : ℝ) / (Fintype.piFinset (fun p : P => S p)).card ≤
      Real.exp (-2 * t ^ 2 / (∑ p ∈ P, (Real.log (p : ℝ)) ^ 2)) := by
  classical
  let : ∀ p : P, Fact p.val.Prime := fun p => ⟨hP p p.property⟩
  let : ∀ p : P, Fintype (ZMod p.val) := fun p => inferInstance
  have hS : ∀ p : P, (S p).Nonempty := by
    intro p
    exact Finset.card_pos.mp (by rw [hcard p p.property]; exact hd)
  have hb : ∀ (p : P) (ρ : ZMod p.val),
      (if (z.1 : ZMod p.val) = ρ * (z.2 : ZMod p.val)
        then Real.log (p.val : ℝ) else 0) ∈ Set.Icc 0 (Real.log (p.val : ℝ)) := by
    intro p ρ
    split_ifs <;> exact ⟨by positivity, by simp [Real.log_natCast_nonneg]⟩
  have htail := box_upper_tail (fun p : P => S p) hS
    (fun p ρ => if (z.1 : ZMod p.val) = ρ * (z.2 : ZMod p.val)
      then Real.log (p.val : ℝ) else 0) (fun p => Real.log (p.val : ℝ)) hb
    (Real.log (A : ℝ) + Real.log (coefficientBound f d : ℝ) / d)
    (average_log_root_hits_growth_le f d hdeg hd P hP S hcard hroot z hprim hz A hA hza hzb)
    t ht
  rw [show (∑ p : P, (Real.log (p.val : ℝ)) ^ 2) =
      ∑ p ∈ P, (Real.log (p : ℝ)) ^ 2 from
        Finset.sum_coe_sort P (fun p : ℕ => (Real.log (p : ℝ)) ^ 2)] at htail
  exact htail

end BinaryFormMoat
