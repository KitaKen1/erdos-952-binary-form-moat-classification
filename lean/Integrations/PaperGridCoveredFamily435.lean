import Integrations.PaperGridInformationExit435
import Integrations.PaperJointCoverage435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- The actual SAME-batch family retains its chosen window bounds, in
addition to the scalar inputs needed to DERIVE coverage on those batches. -/
structure PaperGridCoveredFamily (f : Polynomial ℤ) (R M B : ℕ) (hd : 1 ≤ f.natDegree)
    (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ) : Prop where
  family : PaperGridJointFamily f R M B g0 c a0 l ε bad m P
  spacing : 3 ≤ B
  window : ∀ j ∈ paperGeometricIndices f.natDegree M B,
    paperScheduleX f.natDegree (m j).val ≤ Real.log (B ^ j : ℕ) ∧
    Real.log (B ^ j : ℕ) ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree (m j).val
  inputs : PaperInformationThresholds f.natDegree R M hd g0

/-- Construct the SAME top/middle/bottom batches with ALL coverage scalar
inputs AND the actual chosen window witnesses retained. One threshold is
chosen before every source/law/walk. No alternate coverage batch is selected. -/
theorem paperSchedule_geometric_covered_family (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, 3 ≤ B ∧
        ∀ bad : Finset ℕ, ∀ H : ℝ, ∃ M0 : ℕ, ∀ M ≥ M0,
          ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
            PaperGridCoveredFamily f R M B (by omega) g0 c a0 l ε bad m P ∧
            H ≤ paperGeometricLogBudget f.natDegree M B := by
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hs⟩ := paperSchedule_joint_batches f hf hd R g0 hg0 hg064
  obtain ⟨Mi, hMi⟩ := paperInformationThresholds_eventually f.natDegree R (by omega) g0 hg0 hg064
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l ε hε
  let c0 := ((g0 ^ 2) ^ (l + 1) * a0) / 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  obtain ⟨B, hB, hspacing⟩ := exists_geometric_spacing (2 * c) (ε * c0) (mul_pos hε hc0)
  refine ⟨B, hB, ?_⟩
  intro bad H
  obtain ⟨Mb, hMb⟩ := hs l bad
  have hg := tendsto_paperGeometricLogBudget f.natDegree B (by omega) hB
  obtain ⟨Mg, hMg⟩ := (hg.eventually_ge_atTop H).exists_forall_of_atTop
  obtain ⟨Mn, hMn⟩ := (paperGeometricIndices_eventually_nonempty f.natDegree B (by omega) hB).exists_forall_of_atTop
  refine ⟨Mb + Mi + Mg + Mn, ?_⟩
  intro M hM
  let I := paperGeometricIndices f.natDegree M B
  have hchoose : ∀ j : ℕ, ∃ (m : Fin (M + 1)) (P : Finset ℕ),
      j ∈ I → (M + 1) / 2 ≤ m.val ∧
        paperScheduleX f.natDegree m.val ≤ Real.log (B ^ j : ℕ) ∧
        Real.log (B ^ j : ℕ) ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val ∧
        PaperJointBatch f R M m g0 c a0 l (B ^ j) bad P := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨m, hm, hlo, hhi⟩ := (mem_paperGeometricIndices f.natDegree M B j (by omega) hB).mp hj
      obtain ⟨P, hp⟩ := hMb M (by omega) m hm (B ^ j)
        (paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) hB hj) hlo hhi
      exact ⟨m, P, fun _ => ⟨hm, hlo, hhi, hp⟩⟩
    · exact ⟨0, ∅, fun h => (hj h).elim⟩
  choose m P hP using hchoose
  have hbatch j (hj : j ∈ I) := (hP j hj).2.2.2
  have hI := hMn M (by omega)
  refine ⟨m, P, ⟨⟨?_, ?_, ?_, ?_, hI, ?_⟩, hB, ?_, hMi M (by omega)⟩, hMg M (by omega)⟩
  · exact fun j hj => ⟨(hP j hj).1, hbatch j hj⟩
  · exact geometric_prime_batches_pairwise B hB I P fun j hj p hp =>
      ⟨((hbatch j hj).primes p hp).2.1, ((hbatch j hj).primes p hp).2.2.1⟩
  · apply Finset.disjoint_left.mpr
    intro p hp hbad
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.disjoint_left.mp (hbatch j hj).excluded) hpj hbad
  · intro j hj
    have h := geometric_smaller_weight_sum_small B hB (2 * c) (ε * c0)
      (by positivity) hspacing I
      (fun i => ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ))
      (fun i hi => (hbatch i hi).alphabet) j
    have hr := mul_le_mul_of_nonneg_left (hbatch j hj).recorded_mass hε.le
    change ε * (c0 * (B ^ j : ℕ)) ≤ _ at hr
    exact h.trans (by simpa only [mul_assoc] using hr)
  · exact geometric_prime_union_nonempty _ _ _ P hI fun j hj => (hbatch j hj).nonempty
  · exact fun j hj => ⟨(hP j hj).2.1, (hP j hj).2.2.1⟩

/-- ALL selected batches inherit actual initial-source coverage on one
common terminal experiment, using the chosen window and scalar certificates. -/
theorem PaperGridCoveredFamily.coverage
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (family : PaperGridCoveredFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    [∀ p : P j, NeZero p.val] (e : ∀ p : P j, Q ≃ primeRootSet f p.val)
    (z : ℕ → Point) (a : A → ℕ) (ν : Measure A) (hν : IsProbabilityMeasure ν)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z)
    (i : ℕ) (hi : i ≤ paperCheckpointStop f.natDegree M (B ^ j : ℕ)
      (by have := family.inputs.two; omega)) :
    paperFullTailDeficientFraction (P j) (primeRootSet f) e z f.natDegree M g0 a 0 ν i ≤ paperCoverageEta i := by
  have hp := family.family.batches j hj
  exact PaperJointBatch.initial_coverage f hf hd R M (m j) hp.1 g0 c a0 l (B ^ j)
    (paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) family.spacing hj)
    bad (P j) hp.2 family.inputs (family.window j hj).1 (family.window j hj).2
    e z a ν hν hstep hinj i hi

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridCoveredFamily
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_covered_family
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridCoveredFamily.coverage
