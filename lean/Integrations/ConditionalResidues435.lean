import Integrations.OneStepCoverage435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem lowProbabilityResidues_eq_of_identDistrib {Ω Ω' G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → G) (Y : Ω' → G)
    (h : IdentDistrib X Y μ ν) (τ : ℝ) :
    lowProbabilityResidues μ X τ = lowProbabilityResidues ν Y τ := by
  ext u
  rw [mem_lowProbabilityResidues, mem_lowProbabilityResidues]
  rw [show μ.real (X ⁻¹' {u}) = ν.real (Y ⁻¹' {u}) from
    congrArg ENNReal.toReal (h.measure_mem_eq (MeasurableSet.singleton u))]

theorem lowProbabilityResidues_add_const {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [DecidableEq G] [AddGroup G] (μ : Measure Ω) (X : Ω → G) (g : G) (τ : ℝ) :
    lowProbabilityResidues μ (fun ω => g + X ω) τ =
      (lowProbabilityResidues μ X τ).image (fun u => g + u) := by
  have he : ∀ u, (fun ω => g + X ω) ⁻¹' {g + u} = X ⁻¹' {u} := by
    intro u
    ext ω
    simp
  have hm : ∀ u, g + u ∈ lowProbabilityResidues μ (fun ω => g + X ω) τ ↔
      u ∈ lowProbabilityResidues μ X τ := by
    intro u
    rw [mem_lowProbabilityResidues, mem_lowProbabilityResidues, he]
  ext u
  constructor
  · intro hu
    refine Finset.mem_image.mpr ⟨-g + u, ?_, by simp⟩
    apply (hm (-g + u)).mp
    simpa using hu
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact (hm v).mpr hv

theorem deficientCoordinates_eq_of_identDistrib {Ω Ω' C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype C]
    (μ : Measure Ω) (ν : Measure Ω') (G : C → Type*)
    [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)] [∀ c, MeasurableSingletonClass (G c)]
    (X : ∀ c, Ω → G c) (Y : ∀ c, Ω' → G c)
    (h : ∀ c, IdentDistrib (X c) (Y c) μ ν) (τ β : ℝ) :
    deficientCoordinates μ G X τ β = deficientCoordinates ν G Y τ β := by
  ext c
  rw [mem_deficientCoordinates, mem_deficientCoordinates,
    lowProbabilityResidues_eq_of_identDistrib μ ν (X c) (Y c) (h c) τ]

/-- Translating a terminal conditional law changes the exceptional residues,
but not their count. This supplies displacement coverage to the transfer. -/
theorem lowProbabilityResidues_add_const_card {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [DecidableEq G] [AddGroup G] (μ : Measure Ω) (X : Ω → G) (g : G) (τ : ℝ) :
    (lowProbabilityResidues μ (fun ω => g + X ω) τ).card =
      (lowProbabilityResidues μ X τ).card := by
  rw [lowProbabilityResidues_add_const]
  exact Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.lowProbabilityResidues_eq_of_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.lowProbabilityResidues_add_const
#print axioms BinaryFormMoat.EntropyIntegration.deficientCoordinates_eq_of_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.lowProbabilityResidues_add_const_card
