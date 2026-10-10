import Moat.UniformSampling
import Integrations.PFRInformation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem entropy_uniformOn_finset {Ω : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (C : Finset Ω) (hne : C.Nonempty) :
    entropy id (uniformOn (C : Set Ω)) = Real.log (C.card : ℝ) := by
  let : IsProbabilityMeasure (uniformOn (C : Set Ω)) :=
    isProbabilityMeasure_uniformOn C.finite_toSet hne
  have h := (isUniform_uniformOn (A := (C : Set Ω))).entropy_eq (H := C) measurable_id
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

/-- Exact entropy of the same dependent box used for root selection. -/
theorem entropy_uniformOn_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty) :
    entropy id (uniformOn (Fintype.piFinset S : Set (∀ i, K i))) =
      ∑ i, Real.log ((S i).card : ℝ) := by
  rw [entropy_uniformOn_finset _ (Fintype.piFinset_nonempty.mpr hS), Fintype.card_piFinset]
  push_cast
  exact Real.log_prod (fun i _ => by exact_mod_cast (hS i).card_ne_zero)

theorem uniformOn_box_coordinate_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty) (i : ι) :
    (uniformOn (Fintype.piFinset S : Set (∀ j, K j))).map (fun σ => σ i) =
      uniformOn (S i : Set (K i)) := by
  let : ∀ j, IsProbabilityMeasure (uniformOn (S j : Set (K j))) :=
    fun j => isProbabilityMeasure_uniformOn (S j).finite_toSet (hS j)
  rw [uniformOn_piFinset]
  exact (measurePreserving_eval (fun j => uniformOn (S j : Set (K j))) i).map_eq

theorem entropy_uniformOn_box_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)]
    (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty) (i : ι) :
    entropy (fun σ => σ i) (uniformOn (Fintype.piFinset S : Set (∀ j, K j))) =
      Real.log ((S i).card : ℝ) := by
  rw [entropy_def, uniformOn_box_coordinate_map S hS i]
  simpa only [entropy_def, Measure.map_id] using entropy_uniformOn_finset (S i) (hS i)

/-- The error cost is log of the root count, even in a larger residue field. -/
theorem uniformOn_box_coordinate_information_lower_bound {ι T : Type*}
    [Fintype ι] [DecidableEq ι] {K : ι → Type*} [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (S : ∀ i, Finset (K i)) (hS : ∀ i, (S i).Nonempty) (i : ι)
    (Y : (∀ j, K j) → T) (L : T → Finset (K i)) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : (((Fintype.piFinset S).filter (fun σ => σ i ∉ L (Y σ))).card : ℝ) /
      (Fintype.piFinset S).card ≤ ε) :
    (1 - ε) * Real.log ((S i).card : ℝ) - Real.log 2 - Real.log (M : ℝ) ≤
      mutualInfo (fun σ => σ i) Y (uniformOn (Fintype.piFinset S : Set (∀ j, K j))) := by
  classical
  let : IsProbabilityMeasure (uniformOn (Fintype.piFinset S : Set (∀ j, K j))) :=
    isProbabilityMeasure_uniformOn (Fintype.piFinset S).finite_toSet
      (Fintype.piFinset_nonempty.mpr hS)
  have hu : IsUniform (S i) (fun σ : ∀ j, K j => σ i)
      (uniformOn (Fintype.piFinset S : Set (∀ j, K j))) := by
    apply (isUniform_iff_map_eq_uniformOn _ (measurable_pi_apply i)).mpr
    exact uniformOn_box_coordinate_map S hS i
  apply uniform_mutualInfo_ge_list_size_error_on_support _ _ Y (S i) (hS i) L
    (measurable_pi_apply i) (measurable_of_finite Y) hu M hM hsize ε
  rwa [uniformOn_real_event]

/-- The exact finite-counting law, not an independent replacement measure. -/
theorem uniformOn_real_finset {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (C B : Finset Ω) :
    (uniformOn (C : Set Ω)).real (B : Set Ω) = ((C ∩ B).card : ℝ) / C.card := by
  classical
  have hfilter : C.filter (fun ω => ω ∈ B) = C ∩ B := by ext; simp
  have hset : {ω | ω ∈ B} = (B : Set Ω) := by ext; simp
  have h := uniformOn_real_event C (fun ω => ω ∈ B)
  rwa [hset, hfilter] at h

/-- A counting error certificate directly bounds conditional entropy under
the finite uniform law used by the root-selection calculations. -/
theorem condEntropy_uniformOn_le_list_size_error {Ω S T : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [DecidableEq S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (C : Finset Ω) (hne : C.Nonempty) (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : ((C.filter (fun ω => X ω ∉ L (Y ω))).card : ℝ) / C.card ≤ ε) :
    condEntropy X Y (uniformOn (C : Set Ω)) ≤ Real.log 2 + Real.log (M : ℝ) +
      ε * Real.log (Fintype.card S) := by
  classical
  let : IsProbabilityMeasure (uniformOn (C : Set Ω)) :=
    isProbabilityMeasure_uniformOn C.finite_toSet hne
  apply condEntropy_le_list_size_error _ X Y L (measurable_of_finite _) (measurable_of_finite _)
    M hM hsize ε
  rwa [uniformOn_real_event]

/-- Restricting the same counting law to B pays the size of C intersect B
in the denominator. No post-conditioning independence is asserted. -/
theorem conditioned_uniformOn_condEntropy_le_list_size_error {Ω S T : Type*}
    [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [DecidableEq S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (C B : Finset Ω) (hne : (C ∩ B).Nonempty)
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ y, (L y).card ≤ M) :
    condEntropy X Y ((uniformOn (C : Set Ω))[|(B : Set Ω)]) ≤
      Real.log 2 + Real.log (M : ℝ) +
        (((C.filter (fun ω => X ω ∉ L (Y ω))).card : ℝ) / (C ∩ B).card) *
          Real.log (Fintype.card S) := by
  classical
  have hC : C.Nonempty := hne.mono Finset.inter_subset_left
  let : IsProbabilityMeasure (uniformOn (C : Set Ω)) :=
    isProbabilityMeasure_uniformOn C.finite_toSet hC
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hBCpos : (0 : ℝ) < (C ∩ B).card := by exact_mod_cast hne.card_pos
  have hpos : 0 < (uniformOn (C : Set Ω)).real (B : Set Ω) := by
    rw [uniformOn_real_finset]
    exact div_pos hBCpos hCpos
  have h := conditioned_condEntropy_le_list_size_error (uniformOn (C : Set Ω)) X Y L
    (measurable_of_finite _) (measurable_of_finite _) M hM hsize
    (B : Set Ω) B.measurableSet hpos
    (((C.filter (fun ω => X ω ∉ L (Y ω))).card : ℝ) / C.card)
    (by rw [uniformOn_real_event])
  rw [uniformOn_real_finset] at h
  have hratio : (((C.filter (fun ω => X ω ∉ L (Y ω))).card : ℝ) / C.card) /
      (((C ∩ B).card : ℝ) / C.card) =
      ((C.filter (fun ω => X ω ∉ L (Y ω))).card : ℝ) / (C ∩ B).card := by
    field_simp [hCpos.ne', hBCpos.ne']
  simpa only [hratio] using h

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.uniformOn_real_finset
#print axioms BinaryFormMoat.EntropyIntegration.entropy_uniformOn_finset
#print axioms BinaryFormMoat.EntropyIntegration.entropy_uniformOn_box
#print axioms BinaryFormMoat.EntropyIntegration.uniformOn_box_coordinate_map
#print axioms BinaryFormMoat.EntropyIntegration.entropy_uniformOn_box_coordinate
#print axioms BinaryFormMoat.EntropyIntegration.uniformOn_box_coordinate_information_lower_bound
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_uniformOn_le_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.conditioned_uniformOn_condEntropy_le_list_size_error
