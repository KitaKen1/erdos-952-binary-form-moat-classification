import Integrations.LatticeRay435
import Integrations.LatticeSquaredStep435
import Integrations.PaperPrimeUnionWalkExit435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open FiniteSieveIntegration

/-- The ACTUAL finite prime union now supplies the finite-component sieve
for every Manhattan bound and finite exclusions. The graph bridge and the
squared-step conversion are proved, not supplied as assumptions. -/
theorem irreducible_homogenization_finiteComponentSieve
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    FiniteComponentSieve (f.homogenize f.natDegree) := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  intro D S
  obtain ⟨P, hP, hPS, hno⟩ := paperSchedule_prime_union_excludes_injective_walk f hf hd (2 * D ^ 2) S
  refine ⟨P, hP, hPS, finiteComponents_of_no_injective_lattice_walk _ D ?_⟩
  intro z hz hmem hstep
  apply hno z hz
  · intro n
    apply sqDist_le_of_latticeDist_le D
    rw [latticeDist_symm]
    exact hstep n
  · intro p hp n
    exact hmem n p hp

/-- The existing periodic/disjoint-prime-block exit gives the full arbitrary
prime-budget moat for the homogenized irreducible branch. -/
theorem irreducible_homogenization_uniformMoat_verified
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    UniformMoat (f.homogenize f.natDegree) :=
  uniformMoat_of_finiteComponentSieve _ (irreducible_homogenization_finiteComponentSieve f hf hd)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.irreducible_homogenization_finiteComponentSieve
#print axioms BinaryFormMoat.GeometryIntegration.irreducible_homogenization_uniformMoat_verified
