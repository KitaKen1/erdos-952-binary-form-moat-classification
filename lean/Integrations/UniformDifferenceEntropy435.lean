import Integrations.DifferenceSeparation435
import Integrations.FiniteEntropy435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Uniformity is on distinct elements of H, not on their representing pairs. -/
theorem uniform_subtype_projection_entropy {Q : Type*}
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (H : Finset Point) (hne : H.Nonempty) (F : Point → Q)
    (hinj : Set.InjOn F (H : Set Point)) :
    entropy (fun h : H => F h.val) (uniformOn (Set.univ : Set H)) = Real.log (H.card : ℝ) := by
  classical
  have hH : (Finset.univ : Finset H).Nonempty := by
    obtain ⟨h, hh⟩ := hne
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  have hi : Function.Injective (fun h : H => F h.val) := by
    intro h k he
    exact Subtype.ext (hinj h.property k.property he)
  have h := entropy_comp_of_injective (uniformOn (Set.univ : Set H)) measurable_id
    (fun h : H => F h.val) hi
  simp only [Function.comp_def, id_eq] at h
  rw [h]
  simpa only [Finset.coe_univ, Finset.card_univ, Fintype.card_coe] using
    entropy_uniformOn_finset (Finset.univ : Finset H) hH

def badProjectionIndices {J Q : Type*} [Fintype J]
    (H : Finset Point) (F : J → Point → Q) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => ¬ Set.InjOn (F j) (H : Set Point))

/-- Only the bad root-choice fraction loses entropy; no independence is
inferred inside the point law. Index choices are averaged outside entropy. -/
theorem mean_uniform_projection_entropy_ge {J Q : Type*}
    [Fintype J] [Nonempty J] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (H : Finset Point) (hne : H.Nonempty) (F : J → Point → Q) (ε : ℝ)
    (herr : ((badProjectionIndices H F).card : ℝ) / Fintype.card J ≤ ε) :
    (1 - ε) * Real.log (H.card : ℝ) ≤
      (∑ j, entropy (fun h : H => F j h.val) (uniformOn (Set.univ : Set H))) /
        Fintype.card J := by
  classical
  let good := (Finset.univ : Finset J).filter (fun j => Set.InjOn (F j) (H : Set Point))
  let bad := (Finset.univ : Finset J).filter (fun j => ¬ Set.InjOn (F j) (H : Set Point))
  have hc : good.card + bad.card = Fintype.card J := by
    simpa only [good, bad, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun j => Set.InjOn (F j) (H : Set Point)))
  have hcr : (good.card : ℝ) + bad.card = Fintype.card J := by exact_mod_cast hc
  have hs : (good.card : ℝ) * Real.log (H.card : ℝ) ≤
      ∑ j, entropy (fun h : H => F j h.val) (uniformOn (Set.univ : Set H)) := by
    calc
      _ = ∑ _j ∈ good, Real.log (H.card : ℝ) := by simp
      _ = ∑ j ∈ good, entropy (fun h : H => F j h.val)
          (uniformOn (Set.univ : Set H)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (uniform_subtype_projection_entropy H hne (F j) (Finset.mem_filter.mp hj).2).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
        (fun _ _ _ => entropy_nonneg _ _)
  have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (H.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hne.card_pos)
  have hfrac : 1 - ε ≤ (good.card : ℝ) / Fintype.card J := by
    change (bad.card : ℝ) / Fintype.card J ≤ ε at herr
    have he : (good.card : ℝ) / Fintype.card J + bad.card / Fintype.card J = 1 := by
      rw [← add_div, hcr, div_self hJ.ne']
    linarith
  calc
    _ ≤ ((good.card : ℝ) / Fintype.card J) * Real.log (H.card : ℝ) :=
      mul_le_mul_of_nonneg_right hfrac hlog
    _ = ((good.card : ℝ) * Real.log (H.card : ℝ)) / Fintype.card J := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hJ.le

theorem mean_uniform_projection_condEntropy_ge {J Q O : Type*}
    [Fintype J] [Nonempty J] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (H : Finset Point) (hne : H.Nonempty) (F : J → Point → Q) (Z : J → H → O)
    (ε B : ℝ)
    (herr : ((badProjectionIndices H F).card : ℝ) / Fintype.card J ≤ ε)
    (hobs : ∀ j, entropy (Z j) (uniformOn (Set.univ : Set H)) ≤ B) :
    (1 - ε) * Real.log (H.card : ℝ) - B ≤
      (∑ j, condEntropy (fun h : H => F j h.val) (Z j) (uniformOn (Set.univ : Set H))) /
        Fintype.card J := by
  classical
  have hH : (Set.univ : Set H).Nonempty := by
    obtain ⟨h, hh⟩ := hne
    exact ⟨⟨h, hh⟩, Set.mem_univ _⟩
  let : IsProbabilityMeasure (uniformOn (Set.univ : Set H)) :=
    isProbabilityMeasure_uniformOn (Set.toFinite _) hH
  have h := mean_uniform_projection_entropy_ge H hne F ε herr
  have hs : (∑ j, entropy (fun h : H => F j h.val) (uniformOn (Set.univ : Set H))) -
      (Fintype.card J : ℝ) * B ≤
      ∑ j, condEntropy (fun h : H => F j h.val) (Z j) (uniformOn (Set.univ : Set H)) := by
    have hconst : (Fintype.card J : ℝ) * B = ∑ _j : J, B := by simp
    rw [hconst, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hc := condEntropy_ge_entropy_sub_observation_entropy
      (uniformOn (Set.univ : Set H)) (fun h : H => F j h.val) (Z j)
      (measurable_of_finite _) (measurable_of_finite _)
    linarith [hobs j]
  have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have he : ((∑ j, entropy (fun h : H => F j h.val) (uniformOn (Set.univ : Set H))) -
      (Fintype.card J : ℝ) * B) / Fintype.card J =
      (∑ j, entropy (fun h : H => F j h.val) (uniformOn (Set.univ : Set H))) /
        Fintype.card J - B := by field_simp [hJ.ne']
  have hh := div_le_div_of_nonneg_right hs hJ.le
  rw [he] at hh
  linarith

theorem separated_rootTuple_uniform_entropy (H : Finset Point) (hne : H.Nonempty)
    (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p)) (σ : ∀ p : P, S p)
    (hσ : σ ∉ nonInjectiveRootAssignments H P S) :
    entropy (fun h : H => residueTuple P (fun p => (σ p).val) h.val)
      (uniformOn (Set.univ : Set H)) = Real.log (H.card : ℝ) := by
  classical
  apply uniform_subtype_projection_entropy H hne
  simpa only [nonInjectiveRootAssignments, Finset.mem_filter, Finset.mem_univ,
    true_and, not_not] using hσ

theorem mean_rootTuple_uniform_entropy_ge (H : Finset Point) (hne : H.Nonempty)
    (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p)) (hS : ∀ p : P, (S p).Nonempty)
    (ε : ℝ) (herr : ((nonInjectiveRootAssignments H P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) ≤ ε) :
    (1 - ε) * Real.log (H.card : ℝ) ≤
      (∑ σ : (∀ p : P, S p), entropy
        (fun h : H => residueTuple P (fun p => (σ p).val) h.val)
        (uniformOn (Set.univ : Set H))) / Fintype.card (∀ p : P, S p) := by
  classical
  let : Nonempty (∀ p : P, S p) := ⟨fun p => ⟨(hS p).choose, (hS p).choose_spec⟩⟩
  let F : (∀ p : P, S p) → Point → ((p : P) → ZMod p.val) :=
    fun σ => residueTuple P (fun p => (σ p).val)
  have hb : badProjectionIndices H F = nonInjectiveRootAssignments H P S := by
    ext σ
    simp only [badProjectionIndices, nonInjectiveRootAssignments, Finset.mem_filter,
      Finset.mem_univ, true_and, F]
  have h := mean_uniform_projection_entropy_ge H hne F ε (by rw [hb]; exact herr)
  exact h

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.uniform_subtype_projection_entropy
#print axioms BinaryFormMoat.GeometryIntegration.mean_uniform_projection_entropy_ge
#print axioms BinaryFormMoat.GeometryIntegration.mean_uniform_projection_condEntropy_ge
#print axioms BinaryFormMoat.GeometryIntegration.separated_rootTuple_uniform_entropy
#print axioms BinaryFormMoat.GeometryIntegration.mean_rootTuple_uniform_entropy_ge
