import Integrations.PaperGridCoveredFamily435
import Integrations.RootWordSmoothing435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration MeasureTheory ProbabilityTheory

/-- The already chosen common batch family, with a fixed arithmetic word
threshold reached by ALL selected scales before choosing any walk or law. -/
structure PaperGridRootWordFamily (f : Polynomial ℤ) (R M B : ℕ) (hd : 1 ≤ f.natDegree)
    (g0 c a0 : ℝ) (l : ℕ) (ε : ℝ) (bad : Finset ℕ)
    (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ) : Prop where
  covered : PaperGridCoveredFamily f R M B hd g0 c a0 l ε bad m P
  separation : ∀ j ∈ paperGeometricIndices f.natDegree M B,
    rootWordSeparationThreshold f R ≤ B ^ j

/-- Keep the SAME prime sets and merge the word threshold with the existing
coverage supplier. The spacing is fixed before exclusions and requested
inverse-log budget; the common threshold precedes every source/law/walk. -/
theorem paperSchedule_geometric_root_word_family (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c a0 : ℝ, 0 < c ∧ 0 < a0 ∧ a0 ≤ 1 ∧ a0 ≤ c / 2 ∧
      ∀ l : ℕ, ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, 3 ≤ B ∧
        ∀ bad : Finset ℕ, ∀ H : ℝ, ∃ M0 : ℕ, ∀ M ≥ M0,
          ∃ (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ),
            PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P ∧
            H ≤ paperGeometricLogBudget f.natDegree M B := by
  obtain ⟨c, a0, hc, ha0, ha01, ha0c, hs⟩ :=
    paperSchedule_geometric_covered_family f hf hd R g0 hg0 hg064
  obtain ⟨Mt, ht⟩ := paperSchedule_uniform_batch_threshold f.natDegree (by omega)
    (rootWordSeparationThreshold f R)
  refine ⟨c, a0, hc, ha0, ha01, ha0c, ?_⟩
  intro l ε hε
  obtain ⟨B, hB, hb⟩ := hs l ε hε
  refine ⟨B, hB, ?_⟩
  intro bad H
  obtain ⟨Mc, hm⟩ := hb bad H
  refine ⟨Mc + Mt, ?_⟩
  intro M hM
  obtain ⟨m, P, fam, hbudget⟩ := hm M (by omega)
  refine ⟨m, P, ⟨fam, ?_⟩, hbudget⟩
  intro j hj
  exact ht M (by omega) (m j).val (fam.family.batches j hj).1 (B ^ j) (fam.window j hj).1

/-- Actual geometric dyadic words satisfy ALL separation and terminal
smoothing inputs of the fixed-coordinate passing-list information theorem.
Earlier words divide later words. No supplied word lengths or smoothing
quota remains, and the original chosen batches are retained. -/
theorem PaperGridRootWordFamily.word_inputs
    (f : Polynomial ℤ) (hd : 2 ≤ f.natDegree) (R M B : ℕ) (g0 c a0 : ℝ)
    (l : ℕ) (ε : ℝ) (bad : Finset ℕ) (m : ℕ → Fin (M + 1)) (P : ℕ → Finset ℕ)
    (fam : PaperGridRootWordFamily f R M B (by omega) g0 c a0 l ε bad m P)
    (j : ℕ) (hj : j ∈ paperGeometricIndices f.natDegree M B)
    (p : ℕ) (hp : p ∈ P j) (τ : ℝ) (hτ : (1 : ℝ) / 4 ≤ τ) :
    1 ≤ rootWordLength f.natDegree (B ^ j) ∧
    rootWordLength f.natDegree (B ^ j) ≤ B ^ j ∧
    coefficientBound f f.natDegree * ((R + 1) * rootWordLength f.natDegree (B ^ j)) ^ f.natDegree < p ∧
    (rootWordLength f.natDegree (B ^ j) : ℝ) /
      terminalSmoothingLength (paperScheduleMaxT f.natDegree M) ≤ (τ / p) / 2 ∧
    ∀ i ≤ j, rootWordLength f.natDegree (B ^ i) ∣ rootWordLength f.natDegree (B ^ j) := by
  have hT := paperGeometricIndices_scale_ge_two f.natDegree M B j (by omega) fam.covered.spacing hj
  have hpB := ((fam.covered.family.batches j hj).2.primes p hp)
  have hX := paperScheduleMaxT_ge_stage f.natDegree M (m j).val (by omega)
    (by have := (m j).isLt; omega) (B ^ j : ℕ)
    (by exact_mod_cast (by omega : 0 < B ^ j)) (fam.covered.window j hj).2
  have hT₂ : (2 : ℝ) ≤ (B ^ j : ℕ) := by exact_mod_cast hT
  have hX₂ : (2 : ℝ) ≤ paperScheduleMaxT f.natDegree M := hT₂.trans hX
  refine ⟨rootWordLength_pos _ _, rootWordLength_le _ _ (by omega) (by omega),
    (rootWordLength_separation f R (B ^ j) (by omega) (fam.separation j hj)).trans_le hpB.2.1, ?_, ?_⟩
  · exact rootWord_terminal_smoothing_quota f.natDegree (B ^ j) p (by omega) (by omega)
      (paperScheduleMaxT f.natDegree M) hX₂ hX (by have := hpB.2.1; omega) hpB.2.2.1 τ hτ
  · intro i hi
    exact rootWordLength_dvd _ _ _ (Nat.pow_le_pow_right (by have := fam.covered.spacing; omega) hi)

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_geometric_root_word_family
#print axioms BinaryFormMoat.GeometryIntegration.PaperGridRootWordFamily.word_inputs
