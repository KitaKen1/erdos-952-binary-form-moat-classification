import Integrations.GeometricCoordinateFloor435
import Integrations.ConditionalAverage435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Independent subset/label averaging commutes exactly with a finite weighted mixture. -/
theorem subsetLabelAverage_weighted_sum {ι R A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype A]
    (b : ℕ) (w : A → ℝ) (f : A → Finset ι → (ι → R) → ℝ) :
    subsetLabelAverage b (fun S ρ => ∑ a, w a * f a S ρ) =
      ∑ a, w a * subsetLabelAverage b (f a) := by
  classical
  simp only [subsetLabelAverage, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm]

/-- Mix the exact fiber conditional entropies, then remove the base observation.
Zero-mass fibers are included with their actual zero weights. -/
theorem condEntropy_weighted_fibers_le {Ω S O A : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (P : Ω → O) (B : Ω → A) :
    (∑ a, μ.real (B ⁻¹' {a}) * condEntropy X P (μ[|B ⁻¹' {a}])) ≤
      condEntropy X P μ := by
  rw [← condEntropy_prod_eq_sum μ (measurable_of_finite P) (measurable_of_finite B)]
  exact condEntropy_comp_ge μ (measurable_of_finite (fun ω => (P ω, B ω)))
    (measurable_of_finite X) Prod.fst

end BinaryFormMoat.EntropyIntegration

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Mixture
variable {Ω ι R A : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι] [DecidableEq ι] [Fintype R]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (B : Ω → A) (b : ℕ) (X Y : Ω → Point)

/-- Exact base fibers, subset choices and root labels are averaged before
removing the base condition; no fiber independence is asserted after mixing. -/
theorem labelledPointDifferenceFloor_weighted_fibers_le :
    (∑ a, μ.real (B ⁻¹' {a}) *
      labelledPointDifferenceFloor K F (μ[|B ⁻¹' {a}]) b X Y) ≤
      labelledPointDifferenceFloor K F μ b X Y := by
  classical
  unfold labelledPointDifferenceFloor
  rw [← subsetLabelAverage_weighted_sum]
  apply subsetLabelAverage_mono
  intro S _ ρ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  exact condEntropy_weighted_fibers_le μ (fun ω => F i (ρ i) (X ω - Y ω))
    (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
      residuePrefix K (fun i => F i (ρ i)) S Y ω)) B

/-- Fiber-specific tuple sizes and error bounds may vary with the base;
only their resulting coordinate floors are averaged. -/
theorem labelledPointDifferenceFloor_ge_fiber_floors (hb : b < Fintype.card ι)
    (L : A → ℝ)
    (hfloor : ∀ a, μ.real (B ⁻¹' {a}) ≠ 0 →
      (Fintype.card ι - b : ℕ) * L a ≤
        labelledPointDifferenceFloor K F (μ[|B ⁻¹' {a}]) b X Y) :
    (∑ a, μ.real (B ⁻¹' {a}) * L a) ≤
      labelledPointDifferenceFloor K F μ b X Y / (Fintype.card ι - b : ℕ) := by
  classical
  have hc : (0 : ℝ) < (Fintype.card ι - b : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hb
  apply (le_div_iff₀ hc).mpr
  have hw : (∑ a, μ.real (B ⁻¹' {a}) * L a) * (Fintype.card ι - b : ℕ) ≤
      ∑ a, μ.real (B ⁻¹' {a}) *
        labelledPointDifferenceFloor K F (μ[|B ⁻¹' {a}]) b X Y := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : μ.real (B ⁻¹' {a}) = 0
    · simp [ha]
    · have h := mul_le_mul_of_nonneg_left (hfloor a ha)
        (show 0 ≤ μ.real (B ⁻¹' {a}) from measureReal_nonneg)
      convert h using 1
      ring
  exact hw.trans (labelledPointDifferenceFloor_weighted_fibers_le K F μ B b X Y)

/-- A common positive-fiber floor survives the actual finite base mixture. -/
theorem labelledPointDifferenceFloor_ge_uniform_fiber_floor (hb : b < Fintype.card ι)
    (L : ℝ)
    (hfloor : ∀ a, μ.real (B ⁻¹' {a}) ≠ 0 →
      (Fintype.card ι - b : ℕ) * L ≤
        labelledPointDifferenceFloor K F (μ[|B ⁻¹' {a}]) b X Y) :
    L ≤ labelledPointDifferenceFloor K F μ b X Y / (Fintype.card ι - b : ℕ) := by
  have h := labelledPointDifferenceFloor_ge_fiber_floors K F μ B b X Y hb (fun _ => L) hfloor
  rw [← Finset.sum_mul, fiber_weights_sum_one μ B (measurable_of_finite B), one_mul] at h
  exact h

end Mixture
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_weighted_sum
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_weighted_fibers_le
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointDifferenceFloor_weighted_fibers_le
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointDifferenceFloor_ge_fiber_floors
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointDifferenceFloor_ge_uniform_fiber_floor
