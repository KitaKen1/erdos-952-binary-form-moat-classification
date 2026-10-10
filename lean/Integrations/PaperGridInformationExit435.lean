import Integrations.PaperGridSmoothing435
import Integrations.PaperGeometricFamily435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- An actual nonempty geometric family, retaining all of the certificates
and the same-batch smaller-alphabet budget from the constructed supplier. -/
structure PaperGridJointFamily (f : Polynomial ℤ) (R M B : ℕ) (g0 c a0 : ℝ)
    (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ) : Prop where
  batches : ∀ j ∈ paperGeometricIndices f.natDegree M B,
    (M + 1) / 2 ≤ (m j).val ∧
    PaperJointBatch f R M (m j) g0 c a0 l (B ^ j) bad (P j)
  pairwise : Set.Pairwise (paperGeometricIndices f.natDegree M B : Set ℕ)
    (fun i j => Disjoint (P i) (P j))
  excluded : Disjoint ((paperGeometricIndices f.natDegree M B).biUnion P) bad
  smaller_alphabet : ∀ j ∈ paperGeometricIndices f.natDegree M B,
    (∑ i ∈ (paperGeometricIndices f.natDegree M B).filter (fun i => i < j),
      ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ)) ≤
    ε * ((paperInputRank
      (paperBlockScale f.natDegree M (m j).val g0 0 (a0 * (B ^ j : ℕ)) l)
      (primeBatchLogMean (P j)) : ℝ) * primeBatchLogMean (P j))
  indices_nonempty : (paperGeometricIndices f.natDegree M B).Nonempty
  union_nonempty : ((paperGeometricIndices f.natDegree M B).biUnion P).Nonempty

/-- Arbitrarily large reciprocal-log budgets on ACTUAL nonempty joint
families. B is fixed before bad, the target budget, M and all walks. -/
theorem paperSchedule_geometric_joint_family_large_budget (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ)
    (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, 3 ≤ B ∧
        ∀ bad : Finset ℕ, ∀ H : ℝ, ∃ M0 : ℕ, ∀ M ≥ M0,
          ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
            PaperGridJointFamily f R M B g0 c a0 l ε bad m P ∧
            H ≤ paperGeometricLogBudget f.natDegree M B := by
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hs⟩ :=
    paperSchedule_geometric_joint_family f hf hd R g0 hg0 hg064
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l ε hε
  obtain ⟨B, hB, hfamily⟩ := hs l ε hε
  refine ⟨B, hB, ?_⟩
  intro bad H
  obtain ⟨Mf, hMf⟩ := hfamily bad
  have hg := tendsto_paperGeometricLogBudget f.natDegree B (by omega) hB
  obtain ⟨Mg, hMg⟩ := (hg.eventually_ge_atTop H).exists_forall_of_atTop
  obtain ⟨Mn, hMn⟩ := (paperGeometricIndices_eventually_nonempty f.natDegree B
    (by omega) hB).exists_forall_of_atTop
  refine ⟨Mf + Mg + Mn, ?_⟩
  intro M hM
  obtain ⟨m, P, hp, hpair, hexcl, hsmall⟩ := hMf M (by omega)
  have hI := hMn M (by omega)
  refine ⟨m, P, ⟨hp, hpair, hexcl, hsmall, hI, ?_⟩, hMg M (by omega)⟩
  exact geometric_prime_union_nonempty _ _ _ P hI fun j hj => (hp j hj).2.nonempty

/-- The actual common-law dyadic walk budget excludes a positive grid
lower rate eventually, uniformly in the finite source, law, walk, residue
maps and dyadic lengths. It does NOT prove that the walk has this lower rate.
The threshold is chosen before any of those experiments. -/
theorem paperGrid_walk_word_information_eventually_excluded (d B R : ℕ)
    (hd : 1 ≤ d) (hB : 3 ≤ B) (c : ℝ) (hc : 0 < c) :
    ∃ M0 : ℕ, ∀ M ≥ M0,
      ∀ {Ω G : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
        [Fintype G] [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
        [MeasurableSpace Bool] [MeasurableSingletonClass Bool],
      ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
        (z : ℕ → Point) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
        (φ : ℕ → Point →+ G) (level : ℕ → ℕ), Monotone level →
      ∀ n : ℕ, n ≤ (paperGeometricIndices d M B).card →
        ((2 ^ level n : ℕ) : ℝ) ≤ paperScheduleMaxT d M →
      ¬ c * paperGeometricLogBudget d M B ≤
        (∑ i ∈ Finset.range (n + 1),
          condMutualInfo (fun t => φ i (z t))
            (wordAt (walkLetters z R hstep) (2 ^ level i))
            (observationHistory (fun j t => φ j (z t)) i)
            (smoothedTimeLaw μ b (terminalSmoothingLength (paperScheduleMaxT d M))) /
          (2 ^ level i : ℕ)) := by
  let K := 2 * Real.log (2 * (R + 1) + 1 : ℕ)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * (R + 1) + 1)))
  have hexit := paperGrid_information_budget_eventually_impossible d B hd hB c K hc hK
  obtain ⟨M0, hM0⟩ := hexit.exists_forall_of_atTop
  refine ⟨M0, ?_⟩
  intro M hM Ω G _ _ _ _ _ _ _ _ _ μ _ b z hstep φ level hlevel n hn hlast hlower
  have hT : 1 ≤ paperScheduleMaxT d M := by
    unfold paperScheduleMaxT
    exact Real.one_le_exp (by have h := (paperScheduleX_pos d M hd).le; positivity)
  have hb := smoothedTimeLaw_walk_dyadic_budget μ b z R hstep φ level hlevel n
    (paperScheduleMaxT d M) hT hlast
  have hcost : 0 ≤ (1 + 9 * Real.log (paperScheduleMaxT d M) + K) /
      (paperScheduleMaxT d M) ^ 9 := by
    have hlog := Real.log_nonneg hT
    positivity
  have hnR : (n : ℝ) ≤ ((paperGeometricIndices d M B).card : ℝ) := by exact_mod_cast hn
  apply hM0 M hM
  exact hlower.trans (hb.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right hnR hcost) K))

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridJointFamily
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_joint_family_large_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperGrid_walk_word_information_eventually_excluded
