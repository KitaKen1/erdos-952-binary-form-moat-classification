import Integrations.SmoothedRootPretransport435
import Integrations.OrderedJointBudget435

set_option quotPrecheck false
noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory GeometryIntegration
attribute [local irreducible] paperPassingCount

section Joint
variable {Ω A U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
  (N : ℕ) [NeZero N] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ))
  {M : ℕ} (t : A → Fin M)
  (hforward : ∀ ω : Ω × Fin N, (t (σ ω.1)).val ≤ b ω.1 + ω.2.val)
  (hshift : ∀ ω : Ω × Fin N, b ω.1 + ω.2.val ≤ (t (σ ω.1)).val + S)
  (P : Finset ℕ) [∀ p : P, NeZero p.val] (ρ : ∀ p : P, ZMod p.val)
  (ψ : Point →+ U) (L : ℕ)
local notation "μ" => ν.prod (uniformOn (Set.univ : Set (Fin N)))
local notation "q" => (fun ω : Ω × Fin N => t (σ ω.1))
local notation "u" => (fun ω : Ω × Fin N => b ω.1 + ω.2.val)
local notation "K" => (fun p : P => ZMod p.val)
local notation "φ" => (fun p : P => rootResidueHom p.val (ρ p))
include hforward hshift

/-- The actual selected primes use THEIR natural order and OWN canonical
prefix data. Root passing bounds are DERIVED, not supplied as information
premises. Common quota division precedes one JOINT displacement transport. -/
theorem smoothedRootPackage_joint_gap_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : ∀ p : P, f.eval₂ (Int.castRingHom (ZMod p.val)) (ρ p) = 0)
    (hz : Function.Injective z) (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L)
    (hlo : ∀ p : P, T ≤ p.val) (hhi : ∀ p : P, p.val ≤ 2 * T)
    (hsmall : ∀ p : P, coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p.val)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (herr : ∀ p : P, (L : ℝ) / N ≤ (τ / p.val) / 2)
    (havoid : ∀ p : P, ∀ v, ¬ p.val ∣ (value (f.homogenize f.natDegree) (z v)).natAbs)
    (A : Finset P) :
    let E : P → Set (Ω × Fin N) := fun p => {ω | (p.val : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
      (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ p (z (u ω))) τ).card : ℝ)}
    let V := fun (p : P) (ω : Ω × Fin N) =>
      (φ p (z (q ω).val), orderedPriorHom K φ ψ A p (z (q ω).val))
    let cost := fun p : P => ((1 - β) * Real.log p.val + Real.log 6) +
      (μ).real ((V p) ⁻¹' (posteriorBadData μ (V p) (E p) : Set _)) * (β * Real.log p.val)
    (condEntropy (fun ω => maskedPriorHom K φ A (z (q ω).val)) (fun ω => ψ (z (q ω).val)) μ -
      (∑ p ∈ A, cost p)) / paperPassingCount T L τ β -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      condMutualInfo (fun v => maskedPriorHom K φ A (z v))
        (wordAt (walkLetters z R hstep) L) (fun v => ψ (z v)) ((μ).map u) := by
  dsimp only
  let E : P → Set (Ω × Fin N) := fun p => {ω | (p.val : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
    (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ p (z (u ω))) τ).card : ℝ)}
  let V := fun (p : P) (ω : Ω × Fin N) =>
    (φ p (z (q ω).val), orderedPriorHom K φ ψ A p (z (q ω).val))
  let cost := fun p : P => ((1 - β) * Real.log p.val + Real.log 6) +
    (μ).real ((V p) ⁻¹' (posteriorBadData μ (V p) (E p) : Set _)) * (β * Real.log p.val)
  apply orderedJoint_walk_word_lower_bound K μ z R S hstep q u hforward hshift φ ψ L A
    (paperPassingCount T L τ β : ℝ) (by exact_mod_cast paperPassingCount_pos T L τ β) cost
  intro p _hp
  have hc := smoothedRootPackage_gap_pretransport_lower_bound ν σ b N z R S hstep t
    hforward hshift p.val (ρ p) (orderedPriorHom K φ ψ A p) L f hf hdeg (hρ p) hz
    T hT hL (hlo p) (hhi p) (hsmall p) τ β hτ hβ (herr p) hβ₁ (havoid p)
  dsimp only at hc
  dsimp only [cost, V, E]
  linarith

end Joint

section Natural
variable {Ω U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (r b : Ω → ℕ)
  (N : ℕ) [NeZero N] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ))
  (hforward : ∀ ω : Ω × Fin N, r ω.1 ≤ b ω.1 + ω.2.val)
  (hshift : ∀ ω : Ω × Fin N, b ω.1 + ω.2.val ≤ r ω.1 + S)
  (P : Finset ℕ) [∀ p : P, NeZero p.val] (ρ : ∀ p : P, ZMod p.val)
  (ψ : Point →+ U) (L : ℕ)
local notation "μ" => ν.prod (uniformOn (Set.univ : Set (Fin N)))
local notation "u" => (fun ω : Ω × Fin N => b ω.1 + ω.2.val)
local notation "K" => (fun p : P => ZMod p.val)
local notation "φ" => (fun p : P => rootResidueHom p.val (ρ p))
include hforward hshift

/-- Original natural checkpoint fibers and canonical coordinate data are
retained EXACTLY. There is one joint transport cost, independent of |A|. -/
theorem smoothedRootPackage_joint_exact_gap_lower_bound
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : ∀ p : P, f.eval₂ (Int.castRingHom (ZMod p.val)) (ρ p) = 0)
    (hz : Function.Injective z) (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L)
    (hlo : ∀ p : P, T ≤ p.val) (hhi : ∀ p : P, p.val ≤ 2 * T)
    (hsmall : ∀ p : P, coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p.val)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (herr : ∀ p : P, (L : ℝ) / N ≤ (τ / p.val) / 2)
    (havoid : ∀ p : P, ∀ v, ¬ p.val ∣ (value (f.homogenize f.natDegree) (z v)).natAbs)
    (A : Finset P) :
    let E : P → Set (Ω × Fin N) := fun p =>
      exactCheckpointBadEvent μ (fun ω => r ω.1) (fun _ : Unit => ZMod p.val)
        (fun _ ω => φ p (z (u ω))) τ β ()
    let V := fun (p : P) (ω : Ω × Fin N) =>
      (φ p (z (r ω.1)), orderedPriorHom K φ ψ A p (z (r ω.1)))
    let cost := fun p : P => ((1 - β) * Real.log p.val + Real.log 6) +
      (μ).real ((V p) ⁻¹' (posteriorBadData μ (V p) (E p) : Set _)) * (β * Real.log p.val)
    (condEntropy (fun ω => maskedPriorHom K φ A (z (r ω.1))) (fun ω => ψ (z (r ω.1))) μ -
      (∑ p ∈ A, cost p)) / paperPassingCount T L τ β -
      4 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
      condMutualInfo (fun v => maskedPriorHom K φ A (z v))
        (wordAt (walkLetters z R hstep) L) (fun v => ψ (z v)) ((μ).map u) := by
  have hi := smoothedRootPackage_joint_gap_lower_bound ν (finiteTimeCheckpoint r) b N z R S hstep id
    (by simpa only [id_eq, finiteTimeCheckpoint_val] using hforward)
    (by simpa only [id_eq, finiteTimeCheckpoint_val] using hshift) P ρ ψ L f hf hdeg hρ hz
    T hT hL hlo hhi hsmall τ β hτ hβ hβ₁ herr havoid A
  have hfiber (ω : Ω × Fin N) :
      (fun v : Ω × Fin N => finiteTimeCheckpoint r v.1) ⁻¹' {finiteTimeCheckpoint r ω.1} =
      (fun v : Ω × Fin N => r v.1) ⁻¹' {r ω.1} := by
    change Prod.fst ⁻¹' ((finiteTimeCheckpoint r) ⁻¹' {finiteTimeCheckpoint r ω.1}) = _
    rw [finiteTimeCheckpoint_fiber]
    rfl
  simpa only [id_eq, finiteTimeCheckpoint_val, hfiber, exactCheckpointBadEvent,
    mem_deficientCoordinates, ZMod.card] using hi

end Natural
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_joint_gap_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_joint_exact_gap_lower_bound
