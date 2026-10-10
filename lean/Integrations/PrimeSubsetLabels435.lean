import Integrations.RestrictedLabelAverage435
import Integrations.DifferenceSeparation435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- Convert distinct prime indices back to their actual natural primes. -/
def primeSubset (P : Finset ℕ) (J : Finset P) : Finset ℕ := J.image Subtype.val

theorem primeSubset_card (P : Finset ℕ) (J : Finset P) : (primeSubset P J).card = J.card := by
  unfold primeSubset
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem primeSubset_subset (P : Finset ℕ) (J : Finset P) : primeSubset P J ⊆ P := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact i.property

def primeSubsetEquiv (P : Finset ℕ) (J : Finset P) : J ≃ primeSubset P J :=
  Equiv.ofBijective (fun j => ⟨j.val.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩) (by
    constructor
    · intro i j he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : primeSubset P J => x.val) he
    · intro p
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp p.property
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

theorem primeSubset_sum (P : Finset ℕ) (J : Finset P) (w : ℕ → ℝ) :
    (∑ p ∈ primeSubset P J, w p) = ∑ p ∈ J, w p.val := by
  unfold primeSubset
  exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)

/-- Degree-many roots can be enumerated by one common label type Fin d. -/
def rootLabelEquiv (f : Polynomial ℤ) (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p))
    (hcard : ∀ p ∈ P, (S p).card = f.natDegree) (p : P) : Fin f.natDegree ≃ S p.val :=
  Fintype.equivOfCardEq (by simp [hcard p.val p.property])

def labelledPrimeResidue {R : Type*} (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p))
    (e : ∀ p : P, R ≃ S p.val) : ∀ p : P, R → Point →+ ZMod p.val :=
  fun p ρ => rootResidueHom p.val (e p ρ).val

/-- Reindex local labels by actual primes, then enumerate each local root set. -/
def selectedRootEquiv {R : Type*} (P : Finset ℕ) (S : (p : ℕ) → Finset (ZMod p))
    (e : ∀ p : P, R ≃ S p.val) (J : Finset P) :
    (J → R) ≃ (∀ p : primeSubset P J, S p.val) :=
  (Equiv.piCongrLeft' (fun _ : J => R) (primeSubsetEquiv P J)).trans
    (Equiv.piCongrRight (fun p => e ⟨p.val, primeSubset_subset P J p.property⟩))

theorem selectedRootEquiv_apply {R : Type*} (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, R ≃ S p.val)
    (J : Finset P) (σ : J → R) (j : J) :
    (selectedRootEquiv P S e J σ (primeSubsetEquiv P J j)).val = (e j.val (σ j)).val := by
  simp only [selectedRootEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    Pi.map_apply, Equiv.piCongrLeft'_apply, Equiv.symm_apply_apply]
  rfl

/-- Joint residue injectivity is unchanged by the two exact reindexings. -/
theorem local_prime_projection_injOn_iff {R : Type*} (P : Finset ℕ)
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, R ≃ S p.val)
    (J : Finset P) (σ : J → R) (H : Finset Point) :
    Set.InjOn (fun x (j : J) => labelledPrimeResidue P S e j.val (σ j) x) (H : Set Point) ↔
    Set.InjOn (residueTuple (primeSubset P J) (fun p => (selectedRootEquiv P S e J σ p).val))
      (H : Set Point) := by
  have hcoord (x : Point) (j : J) :
      residueTuple (primeSubset P J) (fun p => (selectedRootEquiv P S e J σ p).val) x
        (primeSubsetEquiv P J j) = labelledPrimeResidue P S e j.val (σ j) x := by
    change rootResidueHom j.val.val
      (selectedRootEquiv P S e J σ (primeSubsetEquiv P J j)).val x = _
    rw [selectedRootEquiv_apply]
    rfl
  constructor
  · intro hinj x hx y hy he
    apply hinj hx hy
    funext j
    exact (hcoord x j).symm.trans ((congrFun he (primeSubsetEquiv P J j)).trans (hcoord y j))
  · intro hinj x hx y hy he
    apply hinj hx hy
    funext p
    obtain ⟨j, rfl⟩ := (primeSubsetEquiv P J).surjective p
    exact (hcoord x j).trans ((congrFun he j).trans (hcoord y j).symm)

/-- Global labels, restricted local labels and actual local root assignments
have the same collision fraction, with no independence/coarsening assumption. -/
theorem global_prime_projection_bad_fraction {R : Type*} [Fintype R] [Nonempty R]
    (P : Finset ℕ) [DecidableEq P] (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, R ≃ S p.val)
    (J : Finset P) (H : Finset Point) :
    (∑ ρ : P → R, if ¬ Set.InjOn
      (labelledSubsetProjection (fun p : P => ZMod p.val)
        (fun p ρ => labelledPrimeResidue P S e p ρ) J ρ) (H : Set Point)
      then (1 : ℝ) else 0) / Fintype.card (P → R) =
    ((nonInjectiveRootAssignments H (primeSubset P J) S).card : ℝ) /
      Fintype.card (∀ p : primeSubset P J, S p.val) := by
  change (∑ ρ : P → R, if ¬ Set.InjOn
    (fun x (j : J) => labelledPrimeResidue P S e j.val (ρ j.val) x) (H : Set Point)
    then (1 : ℝ) else 0) / Fintype.card (P → R) = _
  calc
    _ = (∑ σ : J → R, if ¬ Set.InjOn
        (fun x (j : J) => labelledPrimeResidue P S e j.val (σ j) x) (H : Set Point)
        then (1 : ℝ) else 0) / Fintype.card (J → R) :=
      global_label_mean_restrict J (fun σ : J → R => if ¬ Set.InjOn
        (fun x (j : J) => labelledPrimeResidue P S e j.val (σ j) x) (H : Set Point)
        then (1 : ℝ) else 0)
    _ = (∑ σ : J → R, if ¬ Set.InjOn
        (residueTuple (primeSubset P J) (fun p => (selectedRootEquiv P S e J σ p).val))
        (H : Set Point) then (1 : ℝ) else 0) / Fintype.card (J → R) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hi : Set.InjOn
          (fun x (j : J) => labelledPrimeResidue P S e j.val (σ j) x) (H : Set Point)
      · have hj := (local_prime_projection_injOn_iff P S e J σ H).mp hi
        simp [hi, hj]
      · have hj := mt (local_prime_projection_injOn_iff P S e J σ H).mpr hi
        simp [hi, hj]
    _ = (∑ ρ : (∀ p : primeSubset P J, S p.val), if ¬ Set.InjOn
        (residueTuple (primeSubset P J) (fun p => (ρ p).val))
        (H : Set Point) then (1 : ℝ) else 0) /
        Fintype.card (∀ p : primeSubset P J, S p.val) :=
      finite_mean_equiv (selectedRootEquiv P S e J)
        (fun ρ : (∀ p : primeSubset P J, S p.val) => if ¬ Set.InjOn
          (residueTuple (primeSubset P J) (fun p => (ρ p).val)) (H : Set Point)
          then (1 : ℝ) else 0)
    _ = _ := by
      simp only [nonInjectiveRootAssignments, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one]

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.primeSubset
#print axioms BinaryFormMoat.GeometryIntegration.primeSubset_card
#print axioms BinaryFormMoat.GeometryIntegration.primeSubset_subset
#print axioms BinaryFormMoat.GeometryIntegration.primeSubsetEquiv
#print axioms BinaryFormMoat.GeometryIntegration.primeSubset_sum
#print axioms BinaryFormMoat.GeometryIntegration.rootLabelEquiv
#print axioms BinaryFormMoat.GeometryIntegration.labelledPrimeResidue
#print axioms BinaryFormMoat.GeometryIntegration.selectedRootEquiv
#print axioms BinaryFormMoat.GeometryIntegration.selectedRootEquiv_apply
#print axioms BinaryFormMoat.GeometryIntegration.local_prime_projection_injOn_iff
#print axioms BinaryFormMoat.GeometryIntegration.global_prime_projection_bad_fraction
