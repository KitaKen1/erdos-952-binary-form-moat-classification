import Integrations.SquareBrouwer435
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Normed.Group.Bounded

namespace BinaryFormMoat.GeometryIntegration

/-- Glue matching endpoints through the circle, rather than claiming that
the discontinuous fractional-part map itself is continuous. -/
noncomputable def periodicExtension (f : ℝ → RealPlane) (t : ℝ) : RealPlane :=
  AddCircle.liftIco (1 : ℝ) 0 f (t : AddCircle (1 : ℝ))

theorem periodicExtension_eq_fract (f : ℝ → RealPlane) (t : ℝ) :
    periodicExtension f t = f (Int.fract t) := by
  unfold periodicExtension
  rw [← AddCircle.coe_fract t]
  exact AddCircle.liftIco_zero_coe_apply ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩

theorem continuous_periodicExtension (f : ℝ → RealPlane) (hend : f 0 = f 1)
    (hf : ContinuousOn f (Set.Icc 0 1)) : Continuous (periodicExtension f) := by
  exact (AddCircle.liftIco_zero_continuous hend hf).comp (AddCircle.continuous_mk' 1)

theorem periodicExtension_bounded (f : ℝ → RealPlane)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ t, ‖periodicExtension f t‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ :=
    (isCompact_Icc.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  refine ⟨B, hB, fun t => ?_⟩
  rw [periodicExtension_eq_fract]
  exact hb _ ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩

def pathDeviation (α : ℝ → RealPlane) (t : ℝ) : RealPlane :=
  α t - α 0 - t • (α 1 - α 0)

theorem pathDeviation_endpoints (α : ℝ → RealPlane) :
    pathDeviation α 0 = 0 ∧ pathDeviation α 1 = 0 := by
  simp [pathDeviation]

theorem continuousOn_pathDeviation (α : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) :
    ContinuousOn (pathDeviation α) (Set.Icc 0 1) := by
  exact (hα.sub continuousOn_const).sub (continuousOn_id.smul continuousOn_const)

theorem continuous_periodic_pathDeviation (α : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) :
    Continuous (periodicExtension (pathDeviation α)) := by
  apply continuous_periodicExtension
  · exact (pathDeviation_endpoints α).1.trans (pathDeviation_endpoints α).2.symm
  · exact continuousOn_pathDeviation α hα

noncomputable def pathDeviationPair (α γ : ℝ → RealPlane) (x : RealPlane) : RealPlane :=
  periodicExtension (pathDeviation α) (x 0) -
    periodicExtension (pathDeviation γ) (x 1)

theorem continuous_pathDeviationPair (α γ : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    Continuous (pathDeviationPair α γ) := by
  exact ((continuous_periodic_pathDeviation α hα).comp (continuous_apply 0)).sub
    ((continuous_periodic_pathDeviation γ hγ).comp (continuous_apply 1))

theorem pathDeviationPair_bounded (α γ : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖pathDeviationPair α γ x‖ ≤ B := by
  obtain ⟨A, hA, ha⟩ := periodicExtension_bounded _ (continuousOn_pathDeviation α hα)
  obtain ⟨B, hB, hb⟩ := periodicExtension_bounded _ (continuousOn_pathDeviation γ hγ)
  refine ⟨A + B, add_pos hA hB, fun x => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (ha (x 0)) (hb (x 1)))

/-- Continuous path deviations now supply the bounded perturbation, with no
boundedness premise left. Identifying e with the two endpoint directions and
constructing the integer quotient cover is still needed by moat geometry. -/
theorem path_perturbation_surjective (e : RealPlane ≃L[ℝ] RealPlane)
    (α γ : ℝ → RealPlane) (hα : ContinuousOn α (Set.Icc 0 1))
    (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    Function.Surjective (fun x => e x + pathDeviationPair α γ x) := by
  obtain ⟨B, hB, hb⟩ := pathDeviationPair_bounded α γ hα hγ
  exact bounded_perturbation_surjective e _ (continuous_pathDeviationPair α γ hα hγ)
    B hB.le hb

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.periodicExtension_eq_fract
#print axioms BinaryFormMoat.GeometryIntegration.continuous_periodicExtension
#print axioms BinaryFormMoat.GeometryIntegration.periodicExtension_bounded
#print axioms BinaryFormMoat.GeometryIntegration.pathDeviation_endpoints
#print axioms BinaryFormMoat.GeometryIntegration.continuousOn_pathDeviation
#print axioms BinaryFormMoat.GeometryIntegration.continuous_periodic_pathDeviation
#print axioms BinaryFormMoat.GeometryIntegration.continuous_pathDeviationPair
#print axioms BinaryFormMoat.GeometryIntegration.pathDeviationPair_bounded
#print axioms BinaryFormMoat.GeometryIntegration.path_perturbation_surjective
