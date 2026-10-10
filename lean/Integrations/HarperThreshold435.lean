import Integrations.HarperGrowth435
import Moat.ExpansionBudget

namespace BinaryFormMoat.HarperIntegration

open BooleanIsoperimetry

/-- At radius at least half the dimension, a ball and its complement-image
cover the whole cube. The coarse factor 2 avoids binomial asymptotics. -/
theorem half_cube_le_twice_ball (n t : ℕ) (hnt : n ≤ 2 * t) :
    2 ^ n ≤ 2 * (hammingBall (n := n) t).card := by
  classical
  let B := hammingBall (n := n) t
  have hcover : (Finset.univ : Finset (Cube n)) ⊆ B ∪ B.image (fun x => xᶜ) := by
    intro x _
    by_cases hx : x.card ≤ t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨xᶜ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
      simp only [Finset.card_compl, Fintype.card_fin]
      omega
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have himg : (B.image (fun x => xᶜ)).card ≤ B.card := Finset.card_image_le
  have hfull : (Finset.univ : Finset (Cube n)).card = 2 ^ n := by simp [Cube]
  rw [hfull] at hcard
  change 2 ^ n ≤ 2 * B.card
  omega

/-- Embedding a smaller cube preserves the weight of every vertex. -/
theorem ball_card_mono_dimension (m n t : ℕ) (hmn : m ≤ n) :
    (hammingBall (n := m) t).card ≤ (hammingBall (n := n) t).card := by
  classical
  let e := (Finset.mapEmbedding (Fin.castLEEmb hmn)).toEmbedding
  calc
    _ = ((hammingBall (n := m) t).map e).card := (Finset.card_map _).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [e] using (Finset.mem_filter.mp hx).2

/-- A deliberately coarse explicit lower bound: a radius-t ball in dimension
n>=2t contains at least half a 2t-dimensional cube. -/
theorem ball_card_lower (n t : ℕ) (ht : 2 * t ≤ n) :
    2 ^ (2 * t) ≤ 2 * (hammingBall (n := n) t).card :=
  (half_cube_le_twice_ball (2 * t) t le_rfl).trans
    (Nat.mul_le_mul_left 2 (ball_card_mono_dimension (2 * t) n t ht))

/-- Explicit geometric expansion, capped at a power of two. Neither an
isoperimetric premise nor an unevaluated Hamming-ball size is required. -/
theorem harper_growth_explicit_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) (t r : ℕ) (ht : 2 * t ≤ Fintype.card ι) :
    min ((((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r * A.card)
      ((2 : ℝ) ^ (2 * t) / 2) ≤ (hammingNeighborhood r A).card := by
  have hcap : (2 : ℝ) ^ (2 * t) / 2 ≤ (hammingBall (n := Fintype.card ι) t).card := by
    have h : (2 : ℝ) ^ (2 * t) ≤ 2 * (hammingBall (n := Fintype.card ι) t).card := by
      exact_mod_cast ball_card_lower (Fintype.card ι) t ht
    linarith
  exact (min_le_min_left _ hcap).trans (harper_hamming_growth A t r)

/-- A common density cap gives a common expansion factor for every class.
The remaining schedule problem is the displayed scalar inequality. -/
theorem harper_uniform_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t r : ℕ) (ht : 2 * t ≤ Fintype.card ι) (ε : ℝ)
    (hbudget : (((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r *
      (ε * 2 ^ Fintype.card ι) ≤ (2 : ℝ) ^ (2 * t) / 2)
    (A : Finset (ι → Bool)) (hA : (A.card : ℝ) / 2 ^ Fintype.card ι ≤ ε) :
    (((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r * A.card ≤
      (hammingNeighborhood r A).card := by
  have hA' := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ Fintype.card ι)).mp hA
  have hsmall : (((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r * A.card ≤
      (2 : ℝ) ^ (2 * t) / 2 := by
    exact (mul_le_mul_of_nonneg_left hA' (by positivity)).trans hbudget
  simpa only [min_eq_left hsmall] using harper_growth_explicit_threshold A t r ht

/-- The line-tail interface now requires only a scalar logarithmic budget,
rather than an assumed isoperimetric or expansion theorem. -/
theorem harper_expansion_of_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t r k : ℕ) (ht : 2 * t ≤ Fintype.card ι) (a : ℝ)
    (hg : 0 < ((Fintype.card ι - t : ℕ) : ℝ) / (t + 1))
    (hbudget : (r : ℝ) * Real.log (((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) +
      ((Fintype.card ι : ℝ) - 2 * t + 1) * Real.log 2 ≤ a * k)
    (A : Finset (ι → Bool))
    (hA : (A.card : ℝ) / 2 ^ Fintype.card ι ≤ Real.exp (-a * k)) :
    (((Fintype.card ι - t : ℕ) : ℝ) / (t + 1)) ^ r * A.card ≤
      (hammingNeighborhood r A).card :=
  harper_uniform_expansion t r ht _
    (expansion_budget_of_log _ a hg _ t r k hbudget) A hA

end BinaryFormMoat.HarperIntegration
