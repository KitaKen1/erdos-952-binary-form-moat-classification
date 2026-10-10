import Integrations.PaperFamilyNumerator435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- Choose the fixed all-degree accuracy parameters BEFORE the family,
exclusions, requested budget, all sources and all auxiliary choices. -/
theorem paper_joint_accuracy_parameters (d : ℕ) (hd : 1 ≤ d) :
    ∃ (g0 : ℝ) (l : ℕ) (ε : ℝ), 0 < g0 ∧ g0 < 1 / 64 ∧ 1 ≤ l ∧ 0 < ε ∧
      90 * g0 + (1 / 2 : ℝ) ^ l + ε ≤ paperCheckpointBeta d 0 / 4 := by
  let β := paperCheckpointBeta d 0
  have hb : 0 < β := paperCheckpointBeta_pos d 0 hd
  have hb₁ : β ≤ 1 := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    dsimp only [β, paperCheckpointBeta]
    rw [pow_zero, div_le_iff₀ (by positivity : 0 < 200 * (d : ℝ))]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N, hN⟩ := (hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < β / 8))).exists_forall_of_atTop
  refine ⟨β / 1440, N + 1, β / 16, by positivity, ?_, by omega, by positivity, ?_⟩
  · linarith
  · have h := hN (N + 1) (by omega)
    change 90 * (β / 1440) + (1 / 2 : ℝ) ^ (N + 1) + β / 16 ≤ β / 4
    linarith

/-- A fixed list overhead is absorbed on EVERY admissible batch, using
only the actual schedule's lower window. No log(2)<=g*log(T) is assumed. -/
theorem paperSchedule_uniform_joint_gap (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ∀ T : ℕ, paperScheduleX d m ≤ Real.log T →
        Real.log 6 ≤ paperCheckpointBeta d 0 * Real.log T / 8 := by
  let β := paperCheckpointBeta d 0
  have hb : 0 < β := paperCheckpointBeta_pos d 0 hd
  let C := Nat.ceil (8 * Real.log 6 / β)
  refine ⟨2 * C, ?_⟩
  intro M hM m hm T hlog
  have hC : 8 * Real.log 6 / β ≤ (C : ℝ) := Nat.le_ceil _
  have hCm : (C : ℝ) ≤ m := by exact_mod_cast (by omega : C ≤ m)
  have hx := paperScheduleX_ge_count d m hd
  have hmX : (m : ℝ) ≤ paperScheduleX d m := by linarith [hx]
  have hl := hC.trans (hCm.trans (hmX.trans hlog))
  have h := (div_le_iff₀ hb).mp hl
  change Real.log 6 ≤ β * Real.log T / 8
  linarith

/-- The SAME chosen word family, now with fixed accuracy and list-cost
margins supplied on every selected scale before any probabilistic experiment. -/
structure PaperGridInformationMarginFamily (f : Polynomial ℤ) (R M B : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ) : Prop where
  rootWords : PaperGridRootWordFamily f R M B hd g0 c a0 l ε bad m P
  accuracy : 90 * g0 + (1 / 2 : ℝ) ^ l + ε ≤ paperCheckpointBeta f.natDegree 0 / 4
  gap : ∀ j ∈ paperGeometricIndices f.natDegree M B,
    Real.log 6 ≤ paperCheckpointBeta f.natDegree 0 * Real.log (B ^ j : ℕ) / 8

/-- Fixed parameters and one common threshold supply an actual margin
family with arbitrarily large inverse-log budget. Existing prime sets are
retained when merging thresholds; nothing depends on the walk or its law. -/
theorem paperSchedule_geometric_information_margin_family (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (R : ℕ) :
    ∃ (g0 : ℝ) (l : ℕ) (ε c a0 : ℝ), 0 < g0 ∧ g0 < 1 / 64 ∧ 1 ≤ l ∧ 0 < ε ∧
      0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∃ B : ℕ, 3 ≤ B ∧ ∀ bad : Finset ℕ, ∀ H : ℝ,
        ∃ M0 : ℕ, ∀ M ≥ M0, ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
          PaperGridInformationMarginFamily f R M B (by omega) g0 c a0 l ε bad m P ∧
          H ≤ paperGeometricLogBudget f.natDegree M B := by
  obtain ⟨g0, l, ε, hg0, hg064, hl, hε, hacc⟩ := paper_joint_accuracy_parameters f.natDegree (by omega)
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hs⟩ :=
    paperSchedule_geometric_root_word_family f hf hd R g0 hg0 hg064
  obtain ⟨B, hB, hb⟩ := hs l ε hε
  obtain ⟨Mg, hMg⟩ := paperSchedule_uniform_joint_gap f.natDegree (by omega)
  refine ⟨g0, l, ε, c, a0, hg0, hg064, hl, hε, hc, ha0, ha01, ha0c, B, hB, ?_⟩
  intro bad H
  obtain ⟨Mf, hMf⟩ := hb bad H
  refine ⟨Mf + Mg, ?_⟩
  intro M hM
  obtain ⟨m, P, fam, hbudget⟩ := hMf M (by omega)
  refine ⟨m, P, ⟨fam, hacc, ?_⟩, hbudget⟩
  intro j hj
  exact hMg M (by omega) (m j).val (fam.covered.family.batches j hj).1 (B ^ j)
    (fam.covered.window j hj).1

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paper_joint_accuracy_parameters
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_joint_gap
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridInformationMarginFamily
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_information_margin_family
