import Integrations.PaperInformationMarginFamily435
import Integrations.JointPhysicalMargin435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

def paperJointRecordedConstant (g0 a0 : ℝ) (l : ℕ) : ℝ := ((g0 ^ 2) ^ (l + 1) * a0) / 2
def paperJointRateConstant (d : ℕ) (g0 a0 : ℝ) (l : ℕ) : ℝ :=
  paperCheckpointBeta d 0 * paperJointRecordedConstant g0 a0 l /
    (8 * paperPassingConstant (paperCoverageTau 0) (paperCheckpointBeta d 0))

theorem paperJointRateConstant_pos (d : ℕ) (hd : 1 ≤ d) (g0 a0 : ℝ)
    (hg0 : 0 < g0) (ha0 : 0 < a0) (l : ℕ) : 0 < paperJointRateConstant d g0 a0 l := by
  have hb := paperCheckpointBeta_pos d 0 hd
  have hK := (paperPassingConstant_bounds (paperCoverageTau 0) (paperCheckpointBeta d 0)
    (by norm_num [paperCoverageTau]) hb.le).1
  unfold paperJointRateConstant paperJointRecordedConstant
  positivity

/-- The SAME selected family's actual list checkpoint pays the physical
loss with its native radius. All source-dependent bounds are already derived. -/
theorem PaperGridRootWordFamily.joint_loss_power
    (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree) (R M B : ℕ) (g0 c a0 : ℝ)
    (l : ℕ) (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B) :
    let batch := (fam.covered.family.batches j hj).2
    let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
    let hq : q < (paperScheduleList f.natDegree M g0).length :=
      paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
        (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
    4 * Real.log (2 * ((R + 1) * paperFutureShift
      ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ) ≤
      (2 * (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))) *
        (B ^ j : ℕ) ^ paperCheckpointRadius f.natDegree 0 := by
  dsimp only [paperMiddleStartPosition]
  rw [paperOpPosition_get _ (paperMiddleStartOp_mem f M R (m j)
    (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j)
    ((fam.covered.family.batches j hj).2.middle 0))]
  have hT := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) fam.covered.spacing hj
  have h := paperMiddleStart_native_alphabet f (by omega) M R (m j)
    (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) hT
    (fam.covered.window j hj).1 (fam.covered.window j hj).2
    ((fam.covered.family.batches j hj).2.middle 0) fam.covered.inputs.future
  have he : paperCheckpointTarget f.natDegree (B ^ j : ℕ) 0 =
      (B ^ j : ℕ) ^ paperCheckpointRadius f.natDegree 0 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < B ^ j))]
    simp only [paperCheckpointTarget, mul_comm]
  rw [he] at h
  linarith

/-- A margin family with the ACTUAL physical cost absorbed on every batch. -/
structure PaperGridPositiveRateFamily (f : Polynomial ℤ) (R M B : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ) : Prop where
  margins : PaperGridInformationMarginFamily f R M B hd g0 c a0 l ε bad m P
  physical : ∀ j (hj : j ∈ paperGeometricIndices f.natDegree M B),
    let batch := (margins.rootWords.covered.family.batches j hj).2
    4 * Real.log (2 * ((R + 1) * paperFutureShift
      (paperMiddleStartOp f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0))) + 1 : ℕ) ≤
      paperJointRateConstant f.natDegree g0 a0 l * rootWordLength f.natDegree (B ^ j) /
        Real.log (B ^ j : ℕ)

/-- Fixed positive rate and ONE uniform threshold precede all walks, laws
and auxiliary choices; merge the threshold while retaining the chosen primes. -/
theorem paperSchedule_geometric_positive_rate_family (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (R : ℕ) :
    ∃ (g0 : ℝ) (l : ℕ) (ε c a0 : ℝ), 0 < g0 ∧ g0 < 1 / 64 ∧ 1 ≤ l ∧ 0 < ε ∧
      0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      0 < paperJointRateConstant f.natDegree g0 a0 l ∧
      ∃ B : ℕ, 3 ≤ B ∧ ∀ bad : Finset ℕ, ∀ H : ℝ,
        ∃ M0 : ℕ, ∀ M ≥ M0, ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
          PaperGridPositiveRateFamily f R M B (by omega) g0 c a0 l ε bad m P ∧
          H ≤ paperGeometricLogBudget f.natDegree M B := by
  obtain ⟨g0, l, ε, c, a0, hg0, hg064, hl, hε, hc, ha0, ha01, ha0c, B, hB, hs⟩ :=
    paperSchedule_geometric_information_margin_family f hf hd R
  have hκ := paperJointRateConstant_pos f.natDegree (by omega) g0 a0 hg0 ha0 l
  let C := 2 * (4 + 2 * Real.log (2 * (R + 1) + 1 : ℕ))
  have hC : 0 ≤ C := by
    have hlog := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * (R + 1) + 1) :
      (1 : ℝ) ≤ (2 * (R + 1) + 1 : ℕ))
    dsimp only [C]
    positivity
  obtain ⟨T0, _, ht⟩ := rootWordLength_uniform_physical_margin f.natDegree (by omega)
    C (paperJointRateConstant f.natDegree g0 a0 l) hC hκ
  obtain ⟨Mt, hMt⟩ := paperSchedule_uniform_batch_threshold f.natDegree (by omega) T0
  refine ⟨g0, l, ε, c, a0, hg0, hg064, hl, hε, hc, ha0, ha01, ha0c, hκ, B, hB, ?_⟩
  intro bad H
  obtain ⟨Mf, hMf⟩ := hs bad H
  refine ⟨Mf + Mt, ?_⟩
  intro M hM
  obtain ⟨m, P, fam, hbudget⟩ := hMf M (by omega)
  refine ⟨m, P, ⟨fam, ?_⟩, hbudget⟩
  intro j hj
  have hp := fam.rootWords.joint_loss_power f hd R M B g0 c a0 l ε bad m P j hj
  dsimp only [paperMiddleStartPosition] at hp
  rw [paperOpPosition_get _ (paperMiddleStartOp_mem f M R (m j)
    (fam.rootWords.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j)
    ((fam.rootWords.covered.family.batches j hj).2.middle 0))] at hp
  exact hp.trans (ht (B ^ j) (hMt M (by omega) (m j).val
    (fam.rootWords.covered.family.batches j hj).1 (B ^ j) (fam.rootWords.covered.window j hj).1))

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperJointRecordedConstant
#print axioms BinaryFormMoat.GeometryIntegration.paperJointRateConstant
#print axioms BinaryFormMoat.GeometryIntegration.paperJointRateConstant_pos
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.joint_loss_power
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridPositiveRateFamily
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_positive_rate_family
