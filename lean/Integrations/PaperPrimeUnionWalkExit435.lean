import Integrations.PaperFamilyAverageBudget435
import Integrations.PrimeBlocks435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory FiniteSieveIntegration

/-- Construct the ACTUAL finite prime block before the walk. The same-law
whole-family information sandwich contradicts the divergent geometric grid.
This excludes infinite injective walks; the finite-component bridge remains
a separate obligation and is not assumed here. -/
theorem paperSchedule_prime_union_excludes_injective_walk
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R : ℕ) (bad : Finset ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ Disjoint P bad ∧
      ∀ z : ℕ → Point, Function.Injective z →
        (∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) →
        (∀ p ∈ P, ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs) → False := by
  obtain ⟨g0, l, ε, c, a0, _, _, hl, _, _, ha0, _, _, hκ, B, hB, hs⟩ :=
    paperSchedule_geometric_positive_rate_family f hf hd R
  let K := 2 * Real.log (2 * (R + 1) + 1 : ℕ)
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * (R + 1) + 1)))
  obtain ⟨Me, hMe⟩ := (paperGrid_information_budget_eventually_impossible f.natDegree B (by omega)
    hB (paperJointRateConstant f.natDegree g0 a0 l) K hκ hK).exists_forall_of_atTop
  obtain ⟨Mf, hMf⟩ := hs bad 0
  let M := Mf + Me
  obtain ⟨m, P, fam, _⟩ := hMf M (by dsimp [M]; omega)
  let I := paperGeometricIndices f.natDegree M B
  let U := I.biUnion P
  have hprime : ∀ p ∈ U, p.Prime := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact ((fam.margins.rootWords.covered.family.batches i hi).2.primes p hp).1
  refine ⟨U, hprime, fam.margins.rootWords.covered.family.excluded, ?_⟩
  intro z hz hstep havoid
  let : ∀ i : I, ∀ p : P i.val, NeZero p.val := fun i p =>
    ⟨(((fam.margins.rootWords.covered.family.batches i.val i.property).2.primes p.val p.property).1.ne_zero)⟩
  let ν : Measure (PairedWalkSource Unit (paperScheduleWindow f.natDegree M g0) 0) :=
    Measure.dirac ()
  let : IsProbabilityMeasure ν := ⟨Measure.dirac_apply_of_mem (Set.mem_univ ())⟩
  have hi := fam.information_budget_sandwich f hf hd R M B g0 c a0 ha0.le l hl ε bad m P
    z (fun _ : Unit => 0) ν hstep hz (fun i hi p hp v =>
      havoid p (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩) v)
  exact hMe M (by dsimp [M]; omega) hi

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_prime_union_excludes_injective_walk
