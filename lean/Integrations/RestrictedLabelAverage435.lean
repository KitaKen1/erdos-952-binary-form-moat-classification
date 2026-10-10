import Integrations.SubsetProjection435
import Mathlib.Logic.Equiv.Prod

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration

/-- Restricting globally uniform labels to a subset gives precisely uniform
local labels. Unused coordinates contribute a cancelling factor. -/
theorem global_label_mean_restrict {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype R] [Nonempty R]
    (J : Finset ι) (f : (J → R) → ℝ) :
    (∑ ρ : ι → R, f (fun j => ρ j.val)) / Fintype.card (ι → R) =
      (∑ σ : J → R, f σ) / Fintype.card (J → R) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ J) (fun _ : ι => R)
  have hs : (∑ ρ : ι → R, f (fun j => ρ j.val)) =
      (Fintype.card ({i : ι // i ∉ J} → R) : ℝ) * ∑ σ : J → R, f σ := by
    calc
      _ = ∑ v : (J → R) × ({i : ι // i ∉ J} → R), f v.1 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by simp [Fintype.sum_prod_type, Finset.mul_sum]
  have hc : Fintype.card (ι → R) =
      Fintype.card (J → R) * Fintype.card ({i : ι // i ∉ J} → R) := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  rw [hs, hc, Nat.cast_mul]
  have hn : (Fintype.card ({i : ι // i ∉ J} → R) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem finite_mean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    (∑ a, f (e a)) / Fintype.card A = (∑ b, f b) / Fintype.card B := by
  rw [e.sum_comp, Fintype.card_congr e]

/-- Uniform finite means split an exceptional-index indicator from a good-fiber
failure bound. This is one joint experiment; fiber weights are unchanged. -/
theorem finite_fiber_failure_mean_le {ι R : Type*} [Fintype ι] [Fintype R] [Nonempty R]
    (s : ℕ) (exceptional : Finset ι → Prop) (bad : Finset ι → (ι → R) → Prop)
    [∀ J ρ, Decidable (bad J ρ)]
    (α β : ℝ) (hβ : 0 ≤ β)
    (hex : subsetLabelAverage (R := R) s (fun J _ => if exceptional J then 1 else 0) ≤ α)
    (hgood : ∀ J ∈ (Finset.univ : Finset ι).powersetCard s, ¬ exceptional J →
      (∑ ρ : ι → R, if bad J ρ then (1 : ℝ) else 0) / Fintype.card (ι → R) ≤ β) :
    subsetLabelAverage s (fun J ρ => if bad J ρ then 1 else 0) ≤ α + β := by
  classical
  unfold subsetLabelAverage at hex ⊢
  have hc : (Fintype.card (ι → R) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint : ∀ J ∈ (Finset.univ : Finset ι).powersetCard s,
      (∑ ρ : ι → R, if bad J ρ then (1 : ℝ) else 0) / Fintype.card (ι → R) ≤
      (∑ _ρ : ι → R, if exceptional J then (1 : ℝ) else 0) / Fintype.card (ι → R) + β := by
    intro J hJ
    by_cases hJbad : exceptional J
    · have ht : (∑ ρ : ι → R, if bad J ρ then (1 : ℝ) else 0) ≤ Fintype.card (ι → R) := by
        calc
          _ ≤ ∑ _ρ : ι → R, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
          _ = _ := by simp
      have h := div_le_div_of_nonneg_right ht
        (show (0 : ℝ) ≤ Fintype.card (ι → R) by positivity)
      have h1 : (∑ ρ : ι → R, if bad J ρ then (1 : ℝ) else 0) /
          Fintype.card (ι → R) ≤ 1 := by simpa [hc] using h
      simpa [hJbad, hc] using h1.trans (show (1 : ℝ) ≤ 1 + β by linarith)
    · simpa [hJbad] using hgood J hJ hJbad
  have hsum := Finset.sum_le_sum hpoint
  have hd : (0 : ℝ) ≤ ((Finset.univ : Finset ι).powersetCard s).card := Nat.cast_nonneg _
  have h := div_le_div_of_nonneg_right hsum hd
  rw [Finset.sum_add_distrib, add_div] at h
  have hconst : (∑ _J ∈ (Finset.univ : Finset ι).powersetCard s, β) /
      ((Finset.univ : Finset ι).powersetCard s).card ≤ β := by
    by_cases hz : ((Finset.univ : Finset ι).powersetCard s).card = 0
    · simp [hz, hβ]
    · rw [Finset.sum_const, nsmul_eq_mul]
      exact (mul_div_cancel_left₀ β (by exact_mod_cast hz)).le
  linarith

end BinaryFormMoat.EntropyIntegration
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- The actual bad fraction is the indicator mean over the SAME global labels. -/
theorem badLabelledSubsetFraction_eq_indicator_mean {ι R : Type*} [Fintype ι] [Fintype R]
    (K : ι → Type*) [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (F : ∀ i, R → Point → K i)
    (H : Finset Point) (s : ℕ) :
    badLabelledSubsetFraction K F H s = subsetLabelAverage s (fun J ρ =>
      if ¬ Set.InjOn (labelledSubsetProjection K F J ρ) (H : Set Point) then 1 else 0) := by
  classical
  rw [subsetLabelAverage_eq_choicesMean]
  unfold badLabelledSubsetFraction badLabelledSubsetChoices
  rw [← Finset.sum_filter]
  simp

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.EntropyIntegration.global_label_mean_restrict
#print axioms BinaryFormMoat.EntropyIntegration.finite_mean_equiv
#print axioms BinaryFormMoat.EntropyIntegration.finite_fiber_failure_mean_le
#print axioms BinaryFormMoat.GeometryIntegration.badLabelledSubsetFraction_eq_indicator_mean
