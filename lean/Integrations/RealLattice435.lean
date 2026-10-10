import Integrations.LatticeDifference435
import Integrations.SquareBrouwer435
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace BinaryFormMoat.GeometryIntegration

/-- The actual integer lattice embedded in the real coordinate plane. -/
def realPoint : Point →+ RealPlane where
  toFun a := ![(a.1 : ℝ), (a.2 : ℝ)]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp

theorem realPoint_apply_zero (a : Point) : realPoint a 0 = (a.1 : ℝ) := rfl

theorem realPoint_apply_one (a : Point) : realPoint a 1 = (a.2 : ℝ) := rfl

theorem realPoint_injective : Function.Injective realPoint := by
  intro a b h
  have hx := congrFun h 0
  have hy := congrFun h 1
  apply Prod.ext
  · change (a.1 : ℝ) = (b.1 : ℝ) at hx
    exact_mod_cast hx
  · change (a.2 : ℝ) = (b.2 : ℝ) at hy
    exact_mod_cast hy

def endpointMatrix (a b : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(a.1 : ℝ), -(b.1 : ℝ); (a.2 : ℝ), -(b.2 : ℝ)]

def endpointMap (a b : Point) : RealPlane →L[ℝ] RealPlane :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (endpointMatrix a b))

theorem endpointMap_apply (a b : Point) (x : RealPlane) :
    endpointMap a b x = x 0 • realPoint a - x 1 • realPoint b := by
  ext i
  fin_cases i <;>
    simp [endpointMap, Matrix.toLin'_apply, endpointMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, realPoint] <;> ring

theorem endpointMap_det (a b : Point) :
    (endpointMap a b).det = -((a.1 * b.2 - a.2 * b.1 : ℤ) : ℝ) := by
  rw [endpointMap, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
  simp [endpointMatrix, Matrix.det_fin_two]
  ring

theorem endpointMap_det_ne_zero (a b : Point)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) : (endpointMap a b).det ≠ 0 := by
  rw [endpointMap_det, neg_ne_zero]
  exact_mod_cast hdet

/-- Nonzero integer determinant constructs the real isomorphism needed by Brouwer. -/
def endpointEquiv (a b : Point) (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) :
    RealPlane ≃L[ℝ] RealPlane :=
  (endpointMap a b).toContinuousLinearEquivOfDetNeZero
    (endpointMap_det_ne_zero a b hdet)

theorem endpointEquiv_apply (a b : Point) (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0)
    (x : RealPlane) :
    endpointEquiv a b hdet x = x 0 • realPoint a - x 1 • realPoint b :=
  endpointMap_apply a b x

theorem lattice_integer_translate (a b : Point) (m n : ℤ) :
    m • a - n • b ∈ pointLattice a b := by
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨0, rfl⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨1, rfl⟩

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.realPoint_apply_zero
#print axioms BinaryFormMoat.GeometryIntegration.realPoint_apply_one
#print axioms BinaryFormMoat.GeometryIntegration.realPoint_injective
#print axioms BinaryFormMoat.GeometryIntegration.endpointMap_apply
#print axioms BinaryFormMoat.GeometryIntegration.endpointMap_det
#print axioms BinaryFormMoat.GeometryIntegration.endpointMap_det_ne_zero
#print axioms BinaryFormMoat.GeometryIntegration.endpointEquiv_apply
#print axioms BinaryFormMoat.GeometryIntegration.lattice_integer_translate
