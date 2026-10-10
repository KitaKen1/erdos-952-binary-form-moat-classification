import Integrations.RemainingCoordinate435
import Integrations.SubsetProjection435
import Integrations.LabelledWalkEnrichment435
import Integrations.WalkDifferenceEntropy435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Coordinates
variable {Ω ι R : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Conditional projection entropy averaged over disjoint prefix and extra subsets. -/
def disjointDifferenceTupleEntropy (b r : ℕ) (X Y : Ω → Point) : ℝ :=
  disjointLabelAverage b r (fun S J ρ =>
    condEntropy (fun ω (i : J) => F i.val (ρ i.val) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ)

/-- Prefix information is paid only once for the projected tuple. -/
theorem disjointDifferenceTupleEntropy_ge_unconditioned (b r : ℕ)
    (hbr : b + r ≤ Fintype.card ι) (X Y : Ω → Point) (B : ℝ)
    (hobs : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b, ∀ (ρ : ι → R),
      entropy (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ ≤ B) :
    labelledPointEntropyMean K F μ r (fun ω => X ω - Y ω) - B ≤
      disjointDifferenceTupleEntropy K F μ b r X Y := by
  classical
  have hpoint : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b,
      ∀ J ∈ (Finset.univ \ S).powersetCard r, ∀ (ρ : ι → R),
      entropy (fun ω (i : J) => F i.val (ρ i.val) (X ω - Y ω)) μ - B ≤
        condEntropy (fun ω (i : J) => F i.val (ρ i.val) (X ω - Y ω))
          (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
            residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ := by
    intro S hS J _ ρ
    have h := entropy_sub_observation_le_condEntropy_finite μ
      (fun ω (i : J) => F i.val (ρ i.val) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω))
    linarith [hobs S hS ρ]
  have h := disjointLabelAverage_mono b r _ _ hpoint
  rw [disjointLabelAverage_sub, disjointLabelAverage_ignore_prefix b r hbr,
    disjointLabelAverage_const b r hbr] at h
  exact h

omit [Nonempty R] in
/-- Conditional subadditivity and exact remaining-coordinate inclusion probabilities. -/
theorem disjointDifferenceTupleEntropy_le_coordinate_sum (b r : ℕ) (hr : 1 ≤ r)
    (hbr : b + r ≤ Fintype.card ι) (X Y : Ω → Point) :
    disjointDifferenceTupleEntropy K F μ b r X Y ≤
      ((r : ℝ) / (Fintype.card ι - b : ℕ)) * labelledPointDifferenceFloor K F μ b X Y := by
  classical
  have hpoint : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b, ∀ (ρ : ι → R),
      relativeSubsetMean (Finset.univ \ S) r (fun J =>
        condEntropy (fun ω (i : J) => F i.val (ρ i.val) (X ω - Y ω))
          (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
            residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ) ≤
        (r : ℝ) * (∑ i ∈ Finset.univ \ S,
          condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
            (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
              residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ) /
          (Fintype.card ι - b : ℕ) := by
    intro S hS ρ
    have hSc : (Finset.univ \ S).card = Fintype.card ι - b := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
        (Finset.mem_powersetCard.mp hS).2]
    have hrem : r ≤ (Finset.univ \ S).card := by rw [hSc]; omega
    have h := relativeSubsetMean_condEntropy_le_remaining μ K
      (fun i ω => F i (ρ i) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω)) (Finset.univ \ S) r hr hrem
    rw [hSc] at h
    convert h using 1 <;> first | rfl | ring
  have h := subsetLabelAverage_mono b _ _ hpoint
  have he : ∀ c : ℝ, subsetLabelAverage b
      (fun (S : Finset ι) (ρ : ι → R) => c * (∑ i ∈ Finset.univ \ S,
        condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
          (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
            residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ)) =
      c * labelledPointDifferenceFloor K F μ b X Y := by
    intro c
    simp only [labelledPointDifferenceFloor, subsetLabelAverage,
      Finset.mul_sum, ← mul_div_assoc]
  change disjointDifferenceTupleEntropy K F μ b r X Y ≤ _ at h
  have he' : (fun (S : Finset ι) (ρ : ι → R) => (r : ℝ) * (∑ i ∈ Finset.univ \ S,
        condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
          (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
            residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ) /
          (Fintype.card ι - b : ℕ)) =
      (fun (S : Finset ι) (ρ : ι → R) => ((r : ℝ) / (Fintype.card ι - b : ℕ)) * (∑ i ∈ Finset.univ \ S,
        condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
          (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
            residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ)) := by
    funext S ρ
    ring
  rw [he', he] at h
  exact h

/-- A projected r-tuple entropy floor gives the actual mean of fresh difference coordinates. -/
theorem labelledPointDifferenceFloor_ge_tuple_entropy (b r : ℕ) (hr : 1 ≤ r)
    (hbr : b + r ≤ Fintype.card ι) (X Y : Ω → Point) (A B : ℝ)
    (hjoint : A ≤ labelledPointEntropyMean K F μ r (fun ω => X ω - Y ω))
    (hobs : ∀ S ∈ (Finset.univ : Finset ι).powersetCard b, ∀ (ρ : ι → R),
      entropy (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ ≤ B) :
    (A - B) / r ≤ labelledPointDifferenceFloor K F μ b X Y / (Fintype.card ι - b : ℕ) := by
  have hl := disjointDifferenceTupleEntropy_ge_unconditioned K F μ b r hbr X Y B hobs
  have hu := disjointDifferenceTupleEntropy_le_coordinate_sum K F μ b r hr hbr X Y
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  apply (div_le_iff₀ hrR).mpr
  calc
    A - B ≤ labelledPointEntropyMean K F μ r (fun ω => X ω - Y ω) - B := sub_le_sub_right hjoint B
    _ ≤ _ := hl.trans hu
    _ = _ := by ring

end Coordinates

/-- Exact-base geometric floor from actual uniform distinct differences,
separation failures, finite prefix alphabets, and the walk area bound. -/
theorem uniformWalk_labelledPointDifferenceFloor_ge
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i) (z : ℕ → Point) (D N b r T : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    (hr : 1 ≤ r) (hbr : b + r ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T) (ε : ℝ) (hε : ε ≤ 1)
    (herr : badLabelledSubsetFraction K (fun i a => F i a)
      (pointDifferences (walkVertexSet z N)) r ≤ ε) :
    ((1 - ε) * (Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ)) -
      2 * (b : ℝ) * Real.log (2 * T : ℕ)) / r ≤
    labelledPointDifferenceFloor K F (uniformOn (Set.univ : Set (WalkDifferences z N))) b
      (fun h => z (walkDifferenceTimes z N h).1.val)
      (fun h => z (walkDifferenceTimes z N h).2.val) / (Fintype.card ι - b : ℕ) := by
  classical
  let μ := uniformOn (Set.univ : Set (WalkDifferences z N))
  let X := fun h : WalkDifferences z N => z (walkDifferenceTimes z N h).1.val
  let Y := fun h : WalkDifferences z N => z (walkDifferenceTimes z N h).2.val
  have hdiff : (fun h => X h - Y h) = (fun h : WalkDifferences z N => h.val) :=
    funext (walkDifferenceTimes_spec z N)
  have hproj := labelledSubsetProjectionEntropyMean_ge K (fun i a => F i a)
    _ (walk_differences_nonempty z N) r (by omega) ε herr
  have harea := mul_le_mul_of_nonneg_left (log_prefixArea_le_log_differences z D N hstep hinj)
    (sub_nonneg.mpr hε)
  have hfloor : (1 - ε) * (Real.log (prefixArea z N : ℝ) -
      2 * Real.log (4 * D + 1 : ℕ)) ≤ labelledPointEntropyMean K F μ r (fun h => X h - Y h) := by
    rw [hdiff]
    exact harea.trans hproj
  apply labelledPointDifferenceFloor_ge_tuple_entropy K F μ b r hr hbr X Y _ _ hfloor
  intro S hS ρ
  have hc := (Finset.mem_powersetCard.mp hS).2
  have hx := residuePrefix_entropy_le_log_card_sum K μ (fun i => F i (ρ i)) S X
  have hy := residuePrefix_entropy_le_log_card_sum K μ (fun i => F i (ρ i)) S Y
  have hp := entropy_pair_le_add (measurable_of_finite (residuePrefix K (fun i => F i (ρ i)) S X))
    (measurable_of_finite (residuePrefix K (fun i => F i (ρ i)) S Y)) μ
  have hs : (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
      (b : ℝ) * Real.log (2 * T : ℕ) := by
    calc
      _ ≤ ∑ _i ∈ S, Real.log (2 * T : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.log_le_log (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K i)))
          (by exact_mod_cast hcard i)
      _ = _ := by simp [hc]
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.disjointDifferenceTupleEntropy
#print axioms BinaryFormMoat.GeometryIntegration.disjointDifferenceTupleEntropy_ge_unconditioned
#print axioms BinaryFormMoat.GeometryIntegration.disjointDifferenceTupleEntropy_le_coordinate_sum
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointDifferenceFloor_ge_tuple_entropy
#print axioms BinaryFormMoat.GeometryIntegration.uniformWalk_labelledPointDifferenceFloor_ge
