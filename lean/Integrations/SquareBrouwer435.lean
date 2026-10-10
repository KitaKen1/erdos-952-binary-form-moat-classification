import Integrations.Brouwer435
import Mathlib.Analysis.Normed.Operator.Basic

namespace BinaryFormMoat.GeometryIntegration

abbrev RealPlane := Fin 2 → ℝ
abbrev UnitSegment := Set.Icc (0 : ℝ) 1
abbrev UnitSquare := Fin 2 → UnitSegment
abbrev SimplexSquare := ProductSimplices (fun _ : Fin 2 => (2 : ℕ+))

def segmentSimplex (t : UnitSegment) : Brouwer.standardSimplex ℝ (Fin 2) :=
  ⟨![t.1, 1 - t.1], by
    constructor
    · intro i
      fin_cases i
      · change 0 ≤ t.1
        exact t.2.1
      · change 0 ≤ 1 - t.1
        linarith [t.2.2]
    · simp [Fin.sum_univ_two]⟩

def simplexSegment (x : Brouwer.standardSimplex ℝ (Fin 2)) : UnitSegment :=
  ⟨x.1 0, x.2.1 0, by
    have hs : x.1 0 + x.1 1 = 1 := by simpa [Fin.sum_univ_two] using x.2.2
    linarith [x.2.1 1]⟩

theorem simplexSegment_segmentSimplex (t : UnitSegment) :
    simplexSegment (segmentSimplex t) = t := by
  rfl

theorem continuous_segmentSimplex : Continuous segmentSimplex := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_subtype_val
  · exact continuous_const.sub continuous_subtype_val

theorem continuous_simplexSegment : Continuous simplexSegment := by
  apply Continuous.subtype_mk
  exact (continuous_apply 0).comp continuous_subtype_val

/-- A product-of-simplices fixed point transfers to the closed unit square.
Only the inverse identity needed by this retraction is used. -/
theorem unitSquare_fixed_point (f : UnitSquare → UnitSquare) (hf : Continuous f) :
    ∃ x : UnitSquare, f x = x := by
  let toS : UnitSquare → SimplexSquare := fun x i => segmentSimplex (x i)
  let fromS : SimplexSquare → UnitSquare := fun x i => simplexSegment (x i)
  have hto : Continuous toS := continuous_pi fun i =>
    continuous_segmentSimplex.comp (continuous_apply i)
  have hfrom : Continuous fromS := continuous_pi fun i =>
    continuous_simplexSegment.comp (continuous_apply i)
  have hinv (x : UnitSquare) : fromS (toS x) = x := by
    funext i
    exact simplexSegment_segmentSimplex (x i)
  obtain ⟨x, hx⟩ := Brouwer_Product (card := fun _ : Fin 2 => (2 : ℕ+))
    (toS ∘ f ∘ fromS) (hto.comp (hf.comp hfrom))
  refine ⟨fromS x, ?_⟩
  have he := congrArg fromS hx
  simpa only [Function.comp_apply, hinv] using he

def squarePoint (r : ℝ) (x : UnitSquare) : RealPlane := fun i => 2 * r * (x i).1 - r

theorem squarePoint_bound (r : ℝ) (hr : 0 ≤ r) (x : UnitSquare) (i : Fin 2) :
    |squarePoint r x i| ≤ r := by
  rw [abs_le]
  dsimp [squarePoint]
  constructor <;> nlinarith [(x i).2.1, (x i).2.2]

theorem continuous_squarePoint (r : ℝ) : Continuous (squarePoint r) := by
  apply continuous_pi
  intro i
  exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
    continuous_const

/-- Concrete ambient-square Brouwer theorem, with a positive radius. -/
theorem square_fixed_point (r : ℝ) (hr : 0 < r) (f : RealPlane → RealPlane)
    (hf : Continuous f)
    (hmap : ∀ x, (∀ i, |x i| ≤ r) → ∀ i, |f x i| ≤ r) :
    ∃ x : RealPlane, (∀ i, |x i| ≤ r) ∧ f x = x := by
  let g : UnitSquare → UnitSquare := fun u i =>
    ⟨(f (squarePoint r u) i + r) / (2 * r), by
      have h := (abs_le.mp (hmap _ (squarePoint_bound r hr.le u) i))
      constructor
      · exact div_nonneg (by linarith) (by positivity)
      · apply (div_le_one (by positivity : 0 < 2 * r)).mpr
        linarith⟩
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp (hf.comp (continuous_squarePoint r))).add
      continuous_const).div_const (2 * r)
  obtain ⟨u, hu⟩ := unitSquare_fixed_point g hg
  refine ⟨squarePoint r u, squarePoint_bound r hr.le u, ?_⟩
  ext i
  have he := congrArg (fun v : UnitSquare => (v i).1) hu
  change (f (squarePoint r u) i + r) / (2 * r) = (u i).1 at he
  have he' := (div_eq_iff (by positivity : 2 * r ≠ 0)).mp he
  dsimp [squarePoint]
  linarith

/-- A uniformly bounded continuous perturbation of an invertible planar
linear map is onto. This is the topological engine for the lattice-counting
detour; periodic path gluing remains a separate obligation. -/
theorem bounded_perturbation_surjective (e : RealPlane ≃L[ℝ] RealPlane)
    (H : RealPlane → RealPlane) (hH : Continuous H) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖H x‖ ≤ B) : Function.Surjective (fun x => e x + H x) := by
  intro y
  let A := e.symm.toContinuousLinearMap
  let r := ‖e.symm y‖ + ‖A‖ * B + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let g : RealPlane → RealPlane := fun x => e.symm (y - H x)
  have hg : Continuous g := e.symm.continuous.comp (continuous_const.sub hH)
  have hnorm (x : RealPlane) : ‖g x‖ ≤ r := by
    change ‖e.symm (y - H x)‖ ≤ r
    rw [map_sub]
    have hA : ‖e.symm (H x)‖ ≤ ‖A‖ * B :=
      (A.le_opNorm (H x)).trans (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg A))
    have ht := norm_sub_le (e.symm y) (e.symm (H x))
    dsimp [r]
    linarith
  obtain ⟨x, _, hx⟩ := square_fixed_point r hr g hg (fun x _ i => by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (g x) i).trans (hnorm x))
  refine ⟨x, ?_⟩
  have he := congrArg e hx
  change e (e.symm (y - H x)) = e x at he
  rw [e.apply_symm_apply] at he
  exact (sub_eq_iff_eq_add.mp he).symm

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.simplexSegment_segmentSimplex
#print axioms BinaryFormMoat.GeometryIntegration.continuous_segmentSimplex
#print axioms BinaryFormMoat.GeometryIntegration.continuous_simplexSegment
#print axioms BinaryFormMoat.GeometryIntegration.unitSquare_fixed_point
#print axioms BinaryFormMoat.GeometryIntegration.squarePoint_bound
#print axioms BinaryFormMoat.GeometryIntegration.continuous_squarePoint
#print axioms BinaryFormMoat.GeometryIntegration.square_fixed_point
#print axioms BinaryFormMoat.GeometryIntegration.bounded_perturbation_surjective
