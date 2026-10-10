import Integrations.PosteriorCandidates435
import Integrations.OneStepCoverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Actual candidates without an ORIGINAL translated singleton floor. -/
def translatedCandidateExceptions {Ω C : Type*} [MeasurableSpace Ω] [Fintype C] [AddCommGroup C]
    (μ : Measure Ω) (X : Ω → C) (y : C) (τ : ℝ) : Finset C :=
  Finset.univ.filter (fun x => y - x ∈ lowProbabilityResidues μ X τ)

/-- Translation/reflection is a bijection; the alphabet stays p. -/
theorem translatedCandidateExceptions_card {Ω C : Type*} [MeasurableSpace Ω]
    [Fintype C] [AddCommGroup C] (μ : Measure Ω) (X : Ω → C) (y : C) (τ : ℝ) :
    (translatedCandidateExceptions μ X y τ).card = (lowProbabilityResidues μ X τ).card := by
  apply Finset.card_bij (fun x _ => y - x)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ x' _ h
    have hh := congrArg (fun u => y - u) h
    simpa using hh
  · intro u hu
    refine ⟨y - u, ?_, by simp⟩
    simpa [translatedCandidateExceptions] using hu

theorem translatedCandidateExceptions_floor {Ω C : Type*} [MeasurableSpace Ω]
    [Fintype C] [AddCommGroup C] (μ : Measure Ω) (X : Ω → C) (y : C) (τ : ℝ)
    (x : C) (hx : x ∉ translatedCandidateExceptions μ X y τ) :
    τ / Fintype.card C ≤ μ.real (X ⁻¹' {y - x}) := by
  have hn : y - x ∉ lowProbabilityResidues μ X τ := by
    simpa [translatedCandidateExceptions] using hx
  exact le_of_not_gt (fun h => hn ((mem_lowProbabilityResidues μ X τ _).mpr h))

def singletonCoverageGoodTimes {Ω A C : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype C]
    (μ : Measure Ω) (σ : Ω → A) (X : Ω → C) (τ β : ℝ) : Finset A :=
  Finset.univ.filter (fun a => ((lowProbabilityResidues (μ[|σ ⁻¹' {a}]) X τ).card : ℝ) <
    (Fintype.card C : ℝ) ^ (1 - β))

/-- Favorability yields half posterior good-time mass by complementing the
ORIGINAL exact-time bad event, including all zero-weight branches. -/
theorem singletonCoverageGoodTimes_posterior_mass
    {Ω A D C : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Fintype C] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → A) (F : A → D) (d : D)
    (hd : μ ((F ∘ σ) ⁻¹' {d}) ≠ 0) (X : Ω → C) (τ β : ℝ)
    (hbad : fiberConditionalReal μ (F ∘ σ) d
      {ω | (Fintype.card C : ℝ) ^ (1 - β) ≤
        ((lowProbabilityResidues (μ[|σ ⁻¹' {σ ω}]) X τ).card : ℝ)} ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ (μ[|(F ∘ σ) ⁻¹' {d}]).real
      (σ ⁻¹' (singletonCoverageGoodTimes μ σ X τ β : Set A)) := by
  let : IsProbabilityMeasure (μ[|(F ∘ σ) ⁻¹' {d}]) := cond_isProbabilityMeasure hd
  have he : σ ⁻¹' (singletonCoverageGoodTimes μ σ X τ β : Set A) =
      {ω | (Fintype.card C : ℝ) ^ (1 - β) ≤
        ((lowProbabilityResidues (μ[|σ ⁻¹' {σ ω}]) X τ).card : ℝ)}ᶜ := by
    ext ω
    simp [singletonCoverageGoodTimes]
  rw [he, measureReal_compl (Set.toFinite _).measurableSet, probReal_univ]
  have h := sub_le_sub_left hbad 1
  norm_num [fiberConditionalReal] at h
  exact h

/-- The 4*p^(1-beta) candidate bound follows from ACTUAL favorability and
the ORIGINAL rare-residue sets. No separate deficit budget is assumed. -/
theorem posterior_coverage_exceptional_candidates
    {Ω A D C : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Fintype C] [AddCommGroup C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → A) (F : A → D) (d : D)
    (hd : μ ((F ∘ σ) ⁻¹' {d}) ≠ 0) (X : Ω → C) (Y : A → C) (τ β : ℝ)
    (hbad : fiberConditionalReal μ (F ∘ σ) d
      {ω | (Fintype.card C : ℝ) ^ (1 - β) ≤
        ((lowProbabilityResidues (μ[|σ ⁻¹' {σ ω}]) X τ).card : ℝ)} ≤ (1 : ℝ) / 2) :
    ((Finset.univ.filter (fun x => candidateGoodMass (μ[|(F ∘ σ) ⁻¹' {d}]) σ
      (singletonCoverageGoodTimes μ σ X τ β)
      (fun a => translatedCandidateExceptions (μ[|σ ⁻¹' {a}]) X (Y a) τ) x < (1 : ℝ) / 4)).card : ℝ) ≤
        4 * (Fintype.card C : ℝ) ^ (1 - β) := by
  let : IsProbabilityMeasure (μ[|(F ∘ σ) ⁻¹' {d}]) := cond_isProbabilityMeasure hd
  apply favorable_exceptional_candidates (μ[|(F ∘ σ) ⁻¹' {d}]) σ (measurable_of_finite _)
    (singletonCoverageGoodTimes μ σ X τ β)
    (fun a => translatedCandidateExceptions (μ[|σ ⁻¹' {a}]) X (Y a) τ)
    ((Fintype.card C : ℝ) ^ (1 - β)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (singletonCoverageGoodTimes_posterior_mass μ σ F d hd X τ β hbad)
  intro a ha _
  rw [translatedCandidateExceptions_card]
  exact (Finset.mem_filter.mp ha).2.le

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.translatedCandidateExceptions
#print axioms BinaryFormMoat.EntropyIntegration.translatedCandidateExceptions_card
#print axioms BinaryFormMoat.EntropyIntegration.translatedCandidateExceptions_floor
#print axioms BinaryFormMoat.EntropyIntegration.singletonCoverageGoodTimes
#print axioms BinaryFormMoat.EntropyIntegration.singletonCoverageGoodTimes_posterior_mass
#print axioms BinaryFormMoat.EntropyIntegration.posterior_coverage_exceptional_candidates
