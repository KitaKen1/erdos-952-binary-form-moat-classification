import Integrations.PaperJointRootInformation435
import Integrations.JointInformationAverage435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- Persistent checkpoint entropy and actual backward coverage supply an
averaged JOINT terminal-word bound on the SAME chosen family and original
law. No bad-data, passing-list or information bound is supplied as a premise.
Only the entropy of the arbitrary additive earlier-batch prior is retained. -/
theorem PaperGridRootWordFamily.joint_information_average
    {A Q U : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M B : ℕ) (g0 c a0 : ℝ) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    [∀ p : P j, NeZero p.val] (e : ∀ p : P j, Q ≃ primeRootSet f p.val)
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hstep : ∀ v, sqDist (z (v + 1)) (z v) ≤ (R : ℤ)) (hz : Function.Injective z)
    (ψ : Point →+ U)
    (havoid : ∀ p ∈ P j, ∀ v, ¬ p ∣ (value (f.homogenize f.natDegree) (z v)).natAbs)
    (hbefore : k ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 (m j) 0
      (a0 * (B ^ j : ℕ)) 0 (by have := (fam.covered.family.batches j hj).2.top.fit; omega))) :
    let batch := (fam.covered.family.batches j hj).2
    let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
    let hq : q < (paperScheduleList f.natDegree M g0).length :=
      paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
        (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
    let μ := paperFullTailLaw z f.natDegree M g0 a k ν
    let r := paperFullTailCheckpointTime f.natDegree M g0 a k q hq.le
    let u := paperFullTailTerminalTime f.natDegree M g0 a k
    let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
      (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
    let β := paperCheckpointBeta f.natDegree 0
    let K := fun p : P j => ZMod p.val
    let F := labelledPrimeResidue (P j) (primeRootSet f) e
    (((β - (90 * g0 + (1 / 2 : ℝ) ^ l)) * ((s : ℝ) * primeBatchLogMean (P j)) -
      entropy (fun ω => ψ (z (r ω))) μ - s * Real.log 6 -
      2 * paperCoverageEta 0 * s * Real.log (2 * B ^ j : ℕ) * β) /
        paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β -
      4 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)) ≤
      subsetLabelAverage s (fun C label =>
        condMutualInfo (fun v => maskedPriorHom K (fun p => F p (label p)) C (z v))
          (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
          (fun v => ψ (z v)) (μ.map u)) := by
  let batch := (fam.covered.family.batches j hj).2
  let q := paperMiddleStartPosition f M R (m j) g0 (B ^ j) 0 (P j) (batch.middle 0)
  have hq : q < (paperScheduleList f.natDegree M g0).length :=
    paperOpPosition_lt _ (paperMiddleStartOp_mem f M R (m j)
      (fam.covered.family.batches j hj).1 g0 (B ^ j) 0 (P j) (batch.middle 0))
  let μ := paperFullTailLaw z f.natDegree M g0 a k ν
  let r := paperFullTailCheckpointTime f.natDegree M g0 a k q hq.le
  let u := paperFullTailTerminalTime f.natDegree M g0 a k
  let s := paperInputRank (paperBlockScale f.natDegree M (m j).val g0 0
    (a0 * (B ^ j : ℕ)) l) (primeBatchLogMean (P j))
  let β := paperCheckpointBeta f.natDegree 0
  let K := fun p : P j => ZMod p.val
  let F := labelledPrimeResidue (P j) (primeRootSet f) e
  let φ := fun (label : P j → Q) (p : P j) => F p (label p)
  let V := fun (C : Finset (P j)) (label : P j → Q) (p : P j) ω =>
    (φ label p (z (r ω)), orderedPriorHom K (φ label) ψ C p (z (r ω)))
  let E := exactCheckpointBadEvent μ r (fun p : P j × Q => ZMod p.1.val)
    (fun p ω => F p.1 p.2 (z (u ω))) (paperCoverageTau 0) β
  let H := fun C label => condEntropy
    (fun ω => maskedPriorHom K (φ label) C (z (r ω))) (fun ω => ψ (z (r ω))) μ
  let G := fun (C : Finset (P j)) (_label : P j → Q) =>
    ∑ p ∈ C, ((1 - β) * Real.log (p.val : ℝ) + Real.log 6)
  let D := fun C label => ∑ p ∈ C,
    μ.real ((V C label p) ⁻¹' (posteriorBadData μ (V C label p) (E (p, label p)) : Set _)) *
      (β * Real.log p.val)
  let I := fun C label => condMutualInfo
    (fun v => maskedPriorHom K (φ label) C (z v))
    (wordAt (walkLetters z R hstep) (rootWordLength f.natDegree (B ^ j)))
    (fun v => ψ (z v)) (μ.map u)
  have hm := (fam.covered.family.batches j hj).1
  have hT := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) fam.covered.spacing hj
  have hs : 0 < s ∧ s ≤ (P j).card := by
    simpa only [s, Nat.cast_pow] using
      PaperJointBatch.record_inventory f R M (m j) g0 c a0 l (B ^ j) bad (P j) batch hl hT
  have hmid : k ≤ q := by
    apply hbefore.trans
    apply (paperOpPosition_le_iff _ _
      (paperBlockOp_mem g0 (m j) hm 0 (a0 * (B ^ j : ℕ)) 0 (by have := batch.top.fit; omega))
      (paperMiddleStartOp_mem f M R (m j) hm g0 (B ^ j) 0 (P j) (batch.middle 0))).mpr
    unfold paperOpLater
    right; left
    exact ⟨rfl, by change (0 : Fin 3) < 1; decide⟩
  have hh := PaperJointBatch.middle_start_entropy f hf hd R M (m j) hm g0 c a0 l
    (B ^ j) 0 hl hT bad (P j) batch e z a k ν hbefore hstep hz
  have hp := labelledPointCondEntropyMean_ge K F μ s (by simpa using hs.2)
    (fun ω => z (r ω)) (fun ω => ψ (z (r ω)))
  have he := labelledMaskedCondEntropyMean_eq K F μ s (fun ω => z (r ω)) ψ
  have hH : (1 - 90 * g0 - (1 / 2 : ℝ) ^ l) *
      ((s : ℝ) * primeBatchLogMean (P j)) - entropy (fun ω => ψ (z (r ω))) μ ≤
      subsetLabelAverage s H := by
    change _ ≤ labelledPointEntropyMean K F μ s (fun ω => z (r ω)) at hh
    change subsetLabelAverage s H = _ at he
    rw [he]
    exact (sub_le_sub_right hh _).trans hp
  have hG := subsetLabelAverage_root_gap (P j) (Q := Q) s (by omega) hs.2 β
  have hD := PaperJointBatch.coordinate_bad_beta_log_cost f hf hd R M (m j) hm g0 c a0 l
    (B ^ j) hT bad (P j) batch fam.covered.inputs (fam.covered.window j hj).1
    (fam.covered.window j hj).2 e z a k ν hstep hz 0 (by omega) hmid s (by omega) hs.2
    (fun p => ZMod p.val × (((v : P j) → ZMod v.val) × U)) V
  have hI (C : Finset (P j)) (_hC : C ∈ (Finset.univ : Finset (P j)).powersetCard s)
      (label : P j → Q) := fam.joint_word_information f hf hd R M B g0 c a0 l ε bad m P
        j hj e z a k ν hstep hz ψ C label havoid hmid
  have hE (p : P j) (label : P j → Q) :
      exactCheckpointBadEvent μ r (fun _ : Unit => ZMod p.val)
        (fun _ ω => F p (label p) (z (u ω))) (paperCoverageTau 0) β () = E (p, label p) := by
    ext ω
    simp only [E, exactCheckpointBadEvent, Set.mem_ofPred_eq, mem_deficientCoordinates]
  let loss := 4 * Real.log (2 * ((R + 1) * paperFutureShift
    ((paperScheduleList f.natDegree M g0).get ⟨q, hq⟩)) + 1 : ℕ)
  have ha := joint_package_average_lower_bound s (by simpa using hs.2)
    (paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β : ℝ)
    (by exact_mod_cast paperPassingCount_pos (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β)
    H D G I _ _ _ loss hH hG hD (by
      intro C hC label
      have hc := hI C hC label
      dsimp only at hc
      change (H C label - (∑ p ∈ C,
        (((1 - β) * Real.log (p.val : ℝ) + Real.log 6) +
        μ.real ((V C label p) ⁻¹' (posteriorBadData μ (V C label p)
          (exactCheckpointBadEvent μ r (fun _ : Unit => ZMod p.val)
            (fun _ ω => F p (label p) (z (u ω))) (paperCoverageTau 0) β ()) : Set _)) *
          (β * Real.log p.val)))) /
        paperPassingCount (B ^ j) (rootWordLength f.natDegree (B ^ j)) (paperCoverageTau 0) β -
          loss ≤ I C label at hc
      simp only [hE, Finset.sum_add_distrib] at hc
      simpa only [G, D, Finset.sum_add_distrib] using hc)
  convert ha using 1
  ring

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.joint_information_average
