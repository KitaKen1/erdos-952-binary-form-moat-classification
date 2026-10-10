import Integrations.HarperBridge435
import Moat.NeighborhoodGrowth
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace BinaryFormMoat.HarperIntegration

open BooleanIsoperimetry

/-- Inserting a previously absent coordinate moves by one cube edge. -/
theorem hDist_insert {n : ℕ} (x : Cube n) (i : Fin n) (hi : i ∉ x) :
    hDist x (insert i x) = 1 := by
  have he : symmDiff x (insert i x) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j; simp [Finset.mem_symmDiff, hi]
    · simp [Finset.mem_symmDiff, hj]
  simp [hDist, he]

/-- Upper cube edges expand any family supported in low Hamming layers.
Count each edge once from its lower endpoint and once from its upper endpoint. -/
theorem low_layers_expand {n : ℕ} (A : Finset (Cube n)) (t : ℕ)
    (hA : ∀ x ∈ A, x.card ≤ t) :
    A.card * (n - t) ≤ (neighborhood 1 A).card * (t + 1) := by
  classical
  let rel : Cube n → Cube n → Prop := fun x y => x ⊆ y ∧ x.card + 1 = y.card
  apply Finset.card_mul_le_card_mul rel
  · intro x hx
    calc
      n - t ≤ n - x.card := Nat.sub_le_sub_left (hA x hx) n
      _ = (xᶜ).card := by rw [Finset.card_compl, Fintype.card_fin]
      _ = ((xᶜ).image (fun i => insert i x)).card :=
        (Finset.card_image_of_injOn (Finset.insert_inj_on' x)).symm
      _ ≤ ((neighborhood 1 A).bipartiteAbove rel x).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        have hi' : i ∉ x := Finset.mem_compl.mp hi
        apply (Finset.mem_bipartiteAbove rel).mpr
        exact ⟨mem_neighborhood_iff.mpr ⟨x, hx, (hDist_insert x i hi').le⟩,
          Finset.subset_insert _ _, (Finset.card_insert_of_notMem hi').symm⟩
  · intro y _
    by_cases hne : (A.bipartiteBelow rel y).Nonempty
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨hxA, hxy⟩ := (Finset.mem_bipartiteBelow rel).mp hx
      have hycard : y.card ≤ t + 1 := by
        change x ⊆ y ∧ x.card + 1 = y.card at hxy
        have := hA x hxA
        omega
      calc
        _ ≤ (y.image y.erase).card := by
          apply Finset.card_le_card
          intro u hu
          obtain ⟨_, huy⟩ := (Finset.mem_bipartiteBelow rel).mp hu
          obtain ⟨i, hi, he⟩ := Finset.exists_eq_insert_iff.mpr huy
          apply Finset.mem_image.mpr
          refine ⟨i, he ▸ Finset.mem_insert_self i u, ?_⟩
          rw [← he, Finset.erase_insert hi]
        _ ≤ y.card := Finset.card_image_le
        _ ≤ t + 1 := hycard
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- An initial segment no larger than a radius-t ball cannot enter any layer
above t. This uses only the weight-first ordering, not binomial asymptotics. -/
theorem initial_segment_low_layers (n k t : ℕ) (hk : k ≤ (hammingBall (n := n) t).card) :
    ∀ x ∈ simplicialInitSeg n k, x.card ≤ t := by
  classical
  intro x hx
  have hr : rank x < k := (Finset.mem_filter.mp hx).2
  by_contra hn
  have hball : (hammingBall (n := n) t).card ≤ rank x := by
    apply Finset.card_le_card
    intro y hy
    have hycard : y.card ≤ t := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inl (by omega), ?_⟩
    rintro (h | ⟨h, _⟩) <;> omega
  omega

/-- Explicit radius-one expansion for arbitrary small subsets of the cube.
Harper reduces the problem to the preceding elementary low-layer count. -/
theorem harper_hamming_growth_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) (t : ℕ)
    (hsmall : A.card ≤ (hammingBall (n := Fintype.card ι) t).card) :
    A.card * (Fintype.card ι - t) ≤ (hammingNeighborhood 1 A).card * (t + 1) := by
  have h := low_layers_expand (simplicialInitSeg (Fintype.card ι) A.card) t
    (initial_segment_low_layers _ _ _ hsmall)
  have hcap : A.card ≤ 2 ^ Fintype.card ι := by simpa using Finset.card_le_univ A
  rw [card_simplicialInitSeg, min_eq_left hcap] at h
  exact h.trans (Nat.mul_le_mul_right (t + 1) (harper_hamming_one A))

/-- An explicit geometric growth factor, with an explicit saturation level.
No unproved expansion assumption remains in this theorem. -/
theorem harper_hamming_growth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) (t r : ℕ) :
    min ((((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r * A.card)
      ((hammingBall (n := Fintype.card ι) t).card : ℝ) ≤
        (hammingNeighborhood r A).card := by
  apply hamming_growth_until_threshold _ (by positivity)
  intro B hB
  have h := harper_hamming_growth_one B t hB
  have h' : (B.card : ℝ) * (Fintype.card ι - t : ℕ) ≤
      (hammingNeighborhood 1 B).card * ((t : ℝ) + 1) := by exact_mod_cast h
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < (t : ℝ) + 1)).mpr
  simpa [mul_comm] using h'

end BinaryFormMoat.HarperIntegration
