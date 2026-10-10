import Moat.Obstructions
import Moat.Reduction
import Moat.LinearFactors
import Moat.Factorization
import Integrations.IrreducibleFiniteSieve435

namespace BinaryFormMoat

/-- The irreducible branch, proved by the finite prime sieve and the lattice ray bridge. -/
theorem irreducible_homogenization_uniformMoat (p : Polynomial ℤ)
    (hp : Irreducible p) (hdeg : 2 ≤ p.natDegree) :
    UniformMoat (p.homogenize p.natDegree) := by
  exact GeometryIntegration.irreducible_homogenization_uniformMoat_verified p hp hdeg

/-- The all-degree sufficiency direction after the complete algebraic reduction. -/
theorem uniformMoat_of_not_isLinearPower (F : Form) (d : ℕ) (hF : F ≠ 0)
    (hd : 0 < d) (hhom : F.IsHomogeneous d) (hex : ¬ IsLinearPower F) :
    UniformMoat F :=
  uniformMoat_of_irreducible_case irreducible_homogenization_uniformMoat F d hF hd hhom hex

/-- The classification for every nonzero positive-degree homogeneous binary form. -/
theorem classification (F : Form) (d : ℕ) (hF : F ≠ 0)
    (hd : 0 < d) (hhom : F.IsHomogeneous d) :
    UniformMoat F ↔ ¬ IsLinearPower F :=
  ⟨not_isLinearPower_of_uniformMoat F,
    uniformMoat_of_not_isLinearPower F d hF hd hhom⟩

end BinaryFormMoat

#print axioms BinaryFormMoat.irreducible_homogenization_uniformMoat
#print axioms BinaryFormMoat.uniformMoat_of_not_isLinearPower
#print axioms BinaryFormMoat.classification
