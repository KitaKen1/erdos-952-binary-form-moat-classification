import Integrations.WalkWordCompression435

set_option quotPrecheck false

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

section Smoothed
variable {Ω A U : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
  (N : ℕ) [NeZero N] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ))
  {M : ℕ} (t : A → Fin M)
  (hforward : ∀ ω : Ω × Fin N, (t (σ ω.1)).val ≤ b ω.1 + ω.2.val)
  (hshift : ∀ ω : Ω × Fin N, b ω.1 + ω.2.val ≤ (t (σ ω.1)).val + S)
  (p : ℕ) [NeZero p] (ρ : ZMod p) (ψ : Point →+ U) (L : ℕ)

local notation "μ" => ν.prod (uniformOn (Set.univ : Set (Fin N)))
local notation "q" => (fun ω : Ω × Fin N => t (σ ω.1))
local notation "u" => (fun ω : Ω × Fin N => b ω.1 + ω.2.val)
local notation "φ" => rootResidueHom p ρ
local notation "F" => (fun a : A => (φ (z (t a).val), ψ (z (t a).val)))
local notation "Θ" => walkInformationCheckpointLaw μ z R S hstep q u hforward hshift φ ψ
  (fun ω => wordAt (walkLetters z R hstep) L (u ω))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype U]
  [IsProbabilityMeasure ν] [NeZero N] [NeZero p] in
/-- Exactly the selected target and prior residues are recorded as F(sigma).
The compressed law's positive data fibers are the original data fibers. -/
theorem smoothedRootPackage_fiber (a : ZMod p × U) :
    Θ (Prod.fst ⁻¹' {a}) = μ ((fun ω => F (σ ω.1)) ⁻¹' {a}) :=
  finiteCheckpointLaw_fiber μ _ _ a

/-- The actual finite displacement/word posterior inherits the derived
candidate exceptions and relative-hit floor. Separation and smoothing are
explicit inputs; no compressed hit/cardinality premise is added. -/
theorem smoothedRootPackage_favorable_rejection
    (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (a : ZMod p × U) (ha : Θ (Prod.fst ⁻¹' {a}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 ≤ τ) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (hbad : fiberConditionalReal μ (fun ω => F (σ ω.1)) a
      {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)} ≤
        (1 : ℝ) / 2) :
    ∃ B : Finset (ZMod p), (B.card : ℝ) ≤ 4 * (p : ℝ) ^ (1 - β) ∧
      ∀ x ∉ B, (L : ℝ) * (τ / p) / 8 ≤
        (originalContinuationLaw Θ h₀ a).real {h | wordPackageReject R S L φ x h} := by
  have ha' : μ ((fun ω => F (σ ω.1)) ⁻¹' {a}) ≠ 0 := by
    rwa [smoothedRootPackage_fiber] at ha
  obtain ⟨B, hB, hfloor⟩ := favorable_root_candidate_rejection ν σ b N F a ha'
    f hf hdeg p ρ hρ z hz R hstep (fun a => φ (z (t a).val)) L hsmall τ β hτ herr hbad
  refine ⟨B, hB, ?_⟩
  intro x hx
  rw [walkInformationCheckpointLaw_relative_reject_real μ z R S hstep q u
    hforward hshift φ ψ L h₀ a ha' x]
  simpa only [fiberConditionalReal, sub_eq_add_neg] using hfloor x hx

/-- Same prime-independent quota, now evaluated on the actual compressed
posterior package law rather than on full history/offset sources. -/
theorem smoothedRootPackage_favorable_expected_list
    (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (a : ZMod p × U) (ha : Θ (Prod.fst ⁻¹' {a}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (hz : Function.Injective z)
    (T : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (hbad : fiberConditionalReal μ (fun ω => F (σ ω.1)) a
      {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        (μ[|(fun ω => σ ω.1) ⁻¹' {σ ω.1}]) (fun ω => φ (z (u ω))) τ).card : ℝ)} ≤
        (1 : ℝ) / 2) :
    independentPassingListMean (originalContinuationLaw Θ h₀ a)
      (paperPassingCount T L τ β) (wordPackageReject R S L φ) ≤
        5 * (p : ℝ) ^ (1 - β) := by
  obtain ⟨B, hB, hfloor⟩ := smoothedRootPackage_favorable_rejection ν σ b N z R S hstep t
    hforward hshift p ρ ψ L h₀ a ha f hf hdeg hρ hz hsmall τ β hτ.le herr hbad
  unfold independentPassingListMean
  exact expected_passingList_common_quota (originalContinuationLaw Θ h₀ a)
    T L p hT hL hlo hhi τ β hτ hβ (wordPackageReject R S L φ) B hB hfloor

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Arithmetic zero avoidance and exact (X,O) recording close the true-list
support obligation for the compressed posterior experiment, even on zero
data branches (whose original weights vanish). -/
theorem smoothedRootPackage_avoiding_true_in_list {J : Type*} [Fintype J]
    (h₀ : BoundedDisplacement ((R + 1) * S) × (Fin L → BoundedDisplacement (R + 1)))
    (f : Polynomial ℤ) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (havoid : ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) :
    ∀ᵐ ω ∂originalResamplingLaw (J := J) Θ h₀,
      ω.1.1 ∈ passingList (wordPackageReject R S L φ) ω.2 := by
  exact walkInformationCheckpointLaw_zero_avoiding_true_in_list μ z R S hstep q u
    hforward hshift φ ψ L h₀ (fun v =>
      rootResidueHom_ne_zero_of_not_dvd f f.natDegree le_rfl p ρ hρ (z v) (havoid v))

end Smoothed
end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_fiber
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_favorable_rejection
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_favorable_expected_list
#print axioms BinaryFormMoat.EntropyIntegration.smoothedRootPackage_avoiding_true_in_list
