import Integrations.FiniteJointChain435
import Integrations.WalkPackageRate435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The ACTUAL additive prior for a selected coordinate, including smaller
selected coordinates and the fixed earlier-batch residue prior. -/
def orderedPriorHom {ι U : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [AddCommGroup U]
    (φ : ∀ i, Point →+ K i) (ψ : Point →+ U) (S : Finset ι) (j : ι) :
    Point →+ (((i : ι) → K i) × U) :=
  (maskedPriorHom K φ (orderedCoordinatePrefix S j)).prod ψ

section Budget
variable {Ω ι U H : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, AddCommGroup (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Point)
  (φ : ∀ i, Point →+ K i) (ψ : Point →+ U) (W : Ω → H)

/-- Sum original coordinate package budgets using their ACTUAL fresh
prefixes. No displacement has yet been charged; all terms use one law W. -/
theorem orderedJoint_pretransport_budget (S : Finset ι) (m : ℝ) (cost : ι → ℝ)
    (hcoord : ∀ j ∈ S,
      condEntropy (fun ω => φ j (z ω)) (fun ω => orderedPriorHom K φ ψ S j (z ω)) μ - cost j ≤
        m * condMutualInfo (fun ω => φ j (z ω)) W
          (fun ω => orderedPriorHom K φ ψ S j (z ω)) μ) :
    condEntropy (fun ω => maskedPriorHom K φ S (z ω)) (fun ω => ψ (z ω)) μ -
      (∑ j ∈ S, cost j) ≤
        m * condMutualInfo (fun ω => maskedPriorHom K φ S (z ω)) W (fun ω => ψ (z ω)) μ := by
  have he := maskedPriorHom_ordered_entropy_sum K μ z φ ψ S
  have hi := maskedPriorHom_ordered_information_sum K μ z φ ψ W S
  have hb := Finset.sum_le_sum (fun j hj => hcoord j hj)
  simp only [orderedPriorHom, AddMonoidHom.prod_apply] at hb
  rw [Finset.sum_sub_distrib, he, ← Finset.mul_sum, hi] at hb
  exact hb

end Budget

section Walk
variable {Ω ι U : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
  (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, AddCommGroup (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)
  (φ : ∀ i, Point →+ K i) (ψ : Point →+ U) (L : ℕ)

local notation "P" => (fun ω => (walkDisplacement z R S hstep t u hforward hshift ω,
  wordAt (walkLetters z R hstep) L (u ω)))
include hforward hshift
/-- FIRST aggregate the actual original prefix package information, THEN
transport the joint additive residue vector ONCE. The two displacement
entropy costs are independent of the number of selected coordinates. -/
theorem orderedJoint_walk_word_lower_bound (A : Finset ι) (m : ℝ) (hm : 0 < m)
    (cost : ι → ℝ)
    (hcoord : ∀ j ∈ A,
      condEntropy (fun ω => φ j (z (t ω).val))
        (fun ω => orderedPriorHom K φ ψ A j (z (t ω).val)) μ - cost j ≤
      m * condMutualInfo (fun ω => φ j (z (t ω).val)) P
        (fun ω => orderedPriorHom K φ ψ A j (z (t ω).val)) μ) :
    (condEntropy (fun ω => maskedPriorHom K φ A (z (t ω).val)) (fun ω => ψ (z (t ω).val)) μ -
      (∑ j ∈ A, cost j)) / m - 4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
    condMutualInfo (fun v => maskedPriorHom K φ A (z v))
      (wordAt (walkLetters z R hstep) L) (fun v => ψ (z v)) (μ.map u) := by
  have hj := orderedJoint_pretransport_budget K μ (fun ω => z (t ω).val) φ ψ P A m cost hcoord
  have ht := walk_information_transport μ z R S hstep t u hforward hshift
    (maskedPriorHom K φ A) ψ (fun ω => wordAt (walkLetters z R hstep) L (u ω))
  rw [walk_terminal_word_information_map] at ht
  have hd := (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hj)
  linarith

end Walk
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.orderedPriorHom
#print axioms BinaryFormMoat.EntropyIntegration.orderedJoint_pretransport_budget
#print axioms BinaryFormMoat.EntropyIntegration.orderedJoint_walk_word_lower_bound
