import Integrations.WalkDisplacement435
import Moat.RootSieve

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The actual residue coordinate for a chosen root slope. Its zero fiber
is precisely the congruence lattice used by the arithmetic sieve. -/
def rootResidueHom (p : ℕ) (ρ : ZMod p) : Point →+ ZMod p where
  toFun z := (z.1 : ZMod p) - ρ * (z.2 : ZMod p)
  map_zero' := by simp
  map_add' z w := by
    change ((z.1 + w.1 : ℤ) : ZMod p) - ρ * ((z.2 + w.2 : ℤ) : ZMod p) = _
    simp only [Int.cast_add]
    ring

theorem rootResidueHom_eq_zero_iff (p : ℕ) (ρ : ZMod p) (z : Point) :
    rootResidueHom p ρ z = 0 ↔ (z.1 : ZMod p) = ρ * (z.2 : ZMod p) := by
  exact sub_eq_zero

theorem rootResidueHom_zero_dvd_value (f : Polynomial ℤ) (n : ℕ)
    (hn : f.natDegree ≤ n) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (z : Point)
    (hz : rootResidueHom p ρ z = 0) :
    p ∣ (value (f.homogenize n) z).natAbs :=
  root_line_dvd_value f n hn p ρ hρ z ((rootResidueHom_eq_zero_iff p ρ z).mp hz)

/-- Count one residue-zero hit per prime, rather than per root label. -/
theorem rootResidueHom_hit_count_le (f : Polynomial ℤ) (n : ℕ) (hn : f.natDegree ≤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ρ : (p : ℕ) → ZMod p)
    (hρ : ∀ p ∈ P, f.eval₂ (Int.castRingHom (ZMod p)) (ρ p) = 0)
    (z : Point) (hz : value (f.homogenize n) z ≠ 0) :
    (P.filter (fun p => rootResidueHom p (ρ p) z = 0)).card ≤
      omega (value (f.homogenize n) z) := by
  classical
  simpa only [rootResidueHom_eq_zero_iff] using root_line_hit_count_le f n hn P hP ρ hρ z hz

/-- Degree-many root labels do not multiply the mean coordinate log size.
The actual alphabet of each prime residue has p elements, not d roots. -/
theorem rootResidue_coordinateLogMean {ι Q : Type*} [Fintype ι] [Fintype Q] [Nonempty Q]
    (p : ι → ℕ) [∀ i, NeZero (p i)] :
    coordinateLogMean (fun c : ι × Q => ZMod (p c.1)) =
      (∑ i, Real.log (p i)) / Fintype.card ι := by
  classical
  unfold coordinateLogMean
  simp only [ZMod.card, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_comm (Fintype.card ι : ℝ) (Fintype.card Q : ℝ)]
  exact mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero (α := Q))

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_eq_zero_iff
#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_zero_dvd_value
#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_hit_count_le
#print axioms BinaryFormMoat.EntropyIntegration.rootResidue_coordinateLogMean
