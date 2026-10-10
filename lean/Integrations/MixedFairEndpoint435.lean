import Integrations.LabelledWalkEnrichment435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- One independent fair coin is added AFTER the whole mixed endpoint-pair law. -/
def fairEndpointLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Measure (Ω × Bool) :=
  μ.prod (uniformOn (Set.univ : Set Bool))

instance fairEndpointLaw_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (fairEndpointLaw μ) := by
  unfold fairEndpointLaw
  infer_instance

def fairEndpointPoint {Ω : Type*} (X Y : Ω → Point) (ω : Ω × Bool) : Point :=
  if ω.2 then X ω.1 else Y ω.1

def fairEndpointTime {Ω : Type*} (u v : Ω → ℕ) (ω : Ω × Bool) : ℕ :=
  if ω.2 then u ω.1 else v ω.1

theorem fairEndpointPoint_walk_eq {Ω : Type*} (z : ℕ → Point) (u v : Ω → ℕ) :
    fairEndpointPoint (fun ω => z (u ω)) (fun ω => z (v ω)) =
      (fun ω => z (fairEndpointTime u v ω)) := by
  funext ω
  cases h : ω.2 <;> simp [fairEndpointPoint, fairEndpointTime, h]

theorem fairEndpointTime_bounds {Ω : Type*} (t u v : Ω → ℕ) (N : ℕ)
    (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N) (ω : Ω × Bool) :
    t ω.1 ≤ fairEndpointTime u v ω ∧ fairEndpointTime u v ω ≤ t ω.1 + N := by
  cases h : ω.2 <;> simp only [fairEndpointTime, h, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨htv ω.1, hv ω.1⟩
  · exact ⟨htu ω.1, hu ω.1⟩

/-- Removing an earlier checkpoint from the source never changes the fresh coin.
The identity holds for zero fibers as well. -/
theorem fairEndpointLaw_cond_checkpoint {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Ω → A) (a : A) :
    (fairEndpointLaw μ)[|(fun ω => B ω.1) ⁻¹' {a}] = fairEndpointLaw (μ[|B ⁻¹' {a}]) := by
  have hs : (fun ω : Ω × Bool => B ω.1) ⁻¹' {a} = (B ⁻¹' {a}) ×ˢ Set.univ := by
    ext ω
    simp
  rw [fairEndpointLaw, fairEndpointLaw, hs, ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    Measure.restrict_prod_eq_prod_univ]

section FiniteSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → Point)

/-- Exact fair average on the ORIGINAL mixed source, rather than only on each base. -/
theorem fairEndpointLaw_integral (f : Point → ℝ) :
    ∫ ω, f (fairEndpointPoint X Y ω) ∂fairEndpointLaw μ =
      ((∫ ω, f (X ω) ∂μ) + (∫ ω, f (Y ω) ∂μ)) / 2 := by
  rw [fairEndpointLaw, integral_prod _ Integrable.of_finite]
  have he : ∀ ω : Ω, (∫ c : Bool, f (fairEndpointPoint X Y (ω, c))
      ∂uniformOn (Set.univ : Set Bool)) = (f (X ω) + f (Y ω)) / 2 := by
    intro ω
    rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
    simp only [measureReal_def, uniformOn_univ]
    simp [fairEndpointPoint, smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]

theorem fairEndpointLaw_singleton_average {Q : Type*}
    [MeasurableSpace Q] [MeasurableSingletonClass Q] (F : Point → Q) (q : Q) :
    ((fairEndpointLaw μ).map (fun ω => F (fairEndpointPoint X Y ω))).real {q} =
      ((μ.map (fun ω => F (X ω))).real {q} + (μ.map (fun ω => F (Y ω))).real {q}) / 2 := by
  classical
  have h := fairEndpointLaw_integral μ X Y (fun x => if F x = q then 1 else 0)
  rw [integral_eq_probability_of_eq _ _ (measurable_of_finite _) q,
    integral_eq_probability_of_eq _ _ (measurable_of_finite _) q,
    integral_eq_probability_of_eq _ _ (measurable_of_finite _) q] at h
  exact h

theorem fairEndpointLaw_entropy_ge_half {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q] (F : Point → Q) :
    (entropy (fun ω => F (X ω)) μ + entropy (fun ω => F (Y ω)) μ) / 2 ≤
      entropy (fun ω => F (fairEndpointPoint X Y ω)) (fairEndpointLaw μ) := by
  apply finite_entropy_ge_half_of_singleton_average
  exact fairEndpointLaw_singleton_average μ X Y F

/-- The paper's fair-mixture input for every labelled subset is derived
from the one actual mixed pair source and the independent fair coin. -/
theorem fairEndpointLaw_labelledPointEntropyMean_ge_half
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i) (b : ℕ) :
    (labelledPointEntropyMean K F μ b X + labelledPointEntropyMean K F μ b Y) / 2 ≤
      labelledPointEntropyMean K F (fairEndpointLaw μ) b (fairEndpointPoint X Y) := by
  rw [labelledPointEntropyMean, labelledPointEntropyMean, labelledPointEntropyMean,
    ← subsetLabelAverage_add, ← subsetLabelAverage_div]
  apply subsetLabelAverage_mono
  intro S _ ρ
  exact fairEndpointLaw_entropy_ge_half μ X Y (fun p (i : S) => F i.val (ρ i.val) p)

end FiniteSource
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointPoint
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointTime
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointPoint_walk_eq
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointTime_bounds
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_cond_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_integral
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_singleton_average
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_entropy_ge_half
#print axioms BinaryFormMoat.GeometryIntegration.fairEndpointLaw_labelledPointEntropyMean_ge_half
