import Integrations.PaperJointBatches435
import Integrations.PaperGeometricIndices435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration

/-- Choose B AFTER the fixed top recording constants but BEFORE bad, M,
all used indices and all walks. ALL used powers receive joint-band batches.
The smaller full alphabets cost at most epsilon times the ACTUAL recorded
rank times the TRUE prime-log mean, on the SAME batch. -/
theorem paperSchedule_geometric_joint_family (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, 3 ≤ B ∧
        ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∀ M ≥ M0,
          ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
            (∀ j ∈ paperGeometricIndices f.natDegree M B,
              (M + 1) / 2 ≤ (m j).val ∧
              PaperJointBatch f R M (m j) g0 c a0 l (B ^ j) bad (P j)) ∧
            Set.Pairwise (paperGeometricIndices f.natDegree M B : Set ℕ)
              (fun i j => Disjoint (P i) (P j)) ∧
            Disjoint ((paperGeometricIndices f.natDegree M B).biUnion P) bad ∧
            (∀ j ∈ paperGeometricIndices f.natDegree M B,
              (∑ i ∈ (paperGeometricIndices f.natDegree M B).filter (fun i => i < j),
                ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ)) ≤
              ε * ((paperInputRank
                (paperBlockScale f.natDegree M (m j).val g0 0 (a0 * (B ^ j : ℕ)) l)
                (primeBatchLogMean (P j)) : ℝ) * primeBatchLogMean (P j))) := by
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hs⟩ := paperSchedule_joint_batches f hf hd R g0 hg0 hg064
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l ε hε
  let c0 := ((g0 ^ 2) ^ (l + 1) * a0) / 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  obtain ⟨B, hB, hspacing⟩ := exists_geometric_spacing (2 * c) (ε * c0) (mul_pos hε hc0)
  refine ⟨B, hB, ?_⟩
  intro bad
  obtain ⟨M0, hM0⟩ := hs l bad
  refine ⟨M0, ?_⟩
  intro M hM
  let I := paperGeometricIndices f.natDegree M B
  have hchoose : ∀ j : ℕ, ∃ (m : Fin (M + 1)) (P : Finset ℕ),
      j ∈ I → (M + 1) / 2 ≤ m.val ∧ PaperJointBatch f R M m g0 c a0 l (B ^ j) bad P := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨m, hm, hlo, hhi⟩ := (mem_paperGeometricIndices f.natDegree M B j (by omega) hB).mp hj
      obtain ⟨P, hp⟩ := hM0 M hM m hm (B ^ j)
        (paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) hB hj) hlo hhi
      exact ⟨m, P, fun _ => ⟨hm, hp⟩⟩
    · exact ⟨0, ∅, fun h => (hj h).elim⟩
  choose m P hP using hchoose
  refine ⟨m, P, hP, ?_, ?_, ?_⟩
  · exact geometric_prime_batches_pairwise B hB I P fun j hj p hp =>
      ⟨((hP j hj).2.primes p hp).2.1, ((hP j hj).2.primes p hp).2.2.1⟩
  · apply Finset.disjoint_left.mpr
    intro p hp hbad
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.disjoint_left.mp (hP j hj).2.excluded) hpj hbad
  · intro j hj
    have h := geometric_smaller_weight_sum_small B hB (2 * c) (ε * c0)
      (by positivity) hspacing I
      (fun i => ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ))
      (fun i hi => (hP i hi).2.alphabet) j
    have hr := mul_le_mul_of_nonneg_left (hP j hj).2.recorded_mass hε.le
    change ε * (c0 * (B ^ j : ℕ)) ≤ _ at hr
    exact h.trans (by simpa only [mul_assoc] using hr)

/-- Arithmetic validity survives the actual finite union, without treating
root labels as additional prime coordinates. -/
theorem geometric_joint_family_union_primes (f : Polynomial ℤ) (R M B : ℕ)
    (g0 c a0 : ℝ) (l : ℕ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (hP : ∀ j ∈ paperGeometricIndices f.natDegree M B,
      PaperJointBatch f R M (m j) g0 c a0 l (B ^ j) bad (P j)) :
    ∀ p ∈ (paperGeometricIndices f.natDegree M B).biUnion P,
      p.Prime ∧ (primeRootSet f p).card = f.natDegree := by
  intro p hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
  exact ⟨((hP j hj).primes p hpj).1, ((hP j hj).primes p hpj).2.2.2⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_joint_family
#print axioms BinaryFormMoat.GeometryIntegration.geometric_joint_family_union_primes
