import Integrations.PathDifference435
import Moat.DeterminantGeometry
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration
open scoped unitInterval

/-- A finite prefix of an arbitrary lattice walk, interpolated continuously. -/
def walkPath (z : ℕ → Point) : (n : ℕ) → Path (realPoint (z 0)) (realPoint (z n))
  | 0 => Path.refl _
  | n + 1 => (walkPath z n).trans (Path.segment (realPoint (z n)) (realPoint (z (n + 1))))

theorem coordinate_steps_real (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ j < N, |(z (j + 1)).1 - (z j).1| ≤ D ∧
      |(z (j + 1)).2 - (z j).2| ≤ D) :
    ∀ j < N, ∀ i, |realPoint (z (j + 1)) i - realPoint (z j) i| ≤ (D : ℝ) := by
  intro j hj i
  fin_cases i
  · change |((z (j + 1)).1 : ℝ) - ((z j).1 : ℝ)| ≤ (D : ℝ)
    exact_mod_cast (hstep j hj).1
  · change |((z (j + 1)).2 : ℝ) - ((z j).2 : ℝ)| ≤ (D : ℝ)
    exact_mod_cast (hstep j hj).2

theorem segment_near_source (a b : Point) (D : ℕ)
    (hab : ∀ i, |realPoint b i - realPoint a i| ≤ (D : ℝ)) (t : unitInterval) :
    ∀ i, |Path.segment (realPoint a) (realPoint b) t i - realPoint a i| ≤ (D : ℝ) := by
  intro i
  have he : Path.segment (realPoint a) (realPoint b) t i - realPoint a i =
      (t : ℝ) * (realPoint b i - realPoint a i) := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg t.property.1]
  exact (mul_le_mul_of_nonneg_left (hab i) t.property.1).trans
    (mul_le_of_le_one_left (Nat.cast_nonneg D) t.property.2)

theorem walkPath_range_near_vertex (z : ℕ → Point) (D n : ℕ)
    (hstep : ∀ j < n, ∀ i,
      |realPoint (z (j + 1)) i - realPoint (z j) i| ≤ (D : ℝ)) :
    ∀ y ∈ Set.range (walkPath z n), ∃ j ≤ n,
      ∀ i, |y i - realPoint (z j) i| ≤ (D : ℝ) := by
  induction n with
  | zero =>
      rintro y ⟨t, rfl⟩
      exact ⟨0, le_refl _, by simp [walkPath]⟩
  | succ n ih =>
      intro y hy
      rw [walkPath, Path.trans_range] at hy
      rcases hy with hy | hy
      · obtain ⟨j, hj, hb⟩ := ih (fun j hj => hstep j (by omega)) y hy
        exact ⟨j, by omega, hb⟩
      · obtain ⟨t, rfl⟩ := hy
        exact ⟨n, by omega, segment_near_source _ _ D (hstep n (by omega)) t⟩

/-- Reversing and concatenating prefixes allows any three vertices, regardless
of their order in the walk. No self-avoidance or primitive-vertex premise. -/
def walkBetween (z : ℕ → Point) (i j : ℕ) : Path (realPoint (z i)) (realPoint (z j)) :=
  (walkPath z i).symm.trans (walkPath z j)

theorem walkBetween_near_vertices (E : Finset Point) (z : ℕ → Point) (D N : ℕ)
    (hvertices : ∀ j ≤ N, z j ∈ E)
    (hstep : ∀ j < N, |(z (j + 1)).1 - (z j).1| ≤ D ∧
      |(z (j + 1)).2 - (z j).2| ≤ D)
    (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ E,
      ∀ k, |(walkBetween z i j).extend t k - realPoint v k| ≤ (D : ℝ) := by
  intro t _
  have hr : (walkBetween z i j).extend t ∈ Set.range (walkBetween z i j) := by
    rw [← Path.extend_range]
    exact Set.mem_range_self t
  rw [walkBetween, Path.trans_range, Path.symm_range] at hr
  have hs := coordinate_steps_real z D N hstep
  rcases hr with hr | hr
  · obtain ⟨k, hk, hb⟩ := walkPath_range_near_vertex z D i
      (fun k hk => hs k (by omega)) _ hr
    exact ⟨z k, hvertices k (by omega), hb⟩
  · obtain ⟨k, hk, hb⟩ := walkPath_range_near_vertex z D j
      (fun k hk => hs k (by omega)) _ hr
    exact ⟨z k, hvertices k (by omega), hb⟩

/-- Many differences: every determinant of three vertices of a bounded-step
finite walk is controlled by its difference set. This derives the lattice
cover from the actual walk; collinear triples are included. -/
theorem walk_determinant_le_differences (E : Finset Point) (z : ℕ → Point) (D N : ℕ)
    (hvertices : ∀ j ≤ N, z j ∈ E)
    (hstep : ∀ j < N, |(z (j + 1)).1 - (z j).1| ≤ D ∧
      |(z (j + 1)).2 - (z j).2| ≤ D)
    (i j k : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    ((z j - z i).1 * (z k - z i).2 - (z j - z i).2 * (z k - z i).1).natAbs ≤
      (pointDifferences E).card * (4 * D + 1) ^ 2 := by
  by_cases hd : (z j - z i).1 * (z k - z i).2 - (z j - z i).2 * (z k - z i).1 = 0
  · rw [hd]
    exact Nat.zero_le _
  apply determinant_le_path_differences E (z j - z i) (z k - z i) D hd
    (walkBetween z i j).extend (walkBetween z i k).extend
  · exact (walkBetween z i j).continuous_extend.continuousOn
  · exact (walkBetween z i k).continuous_extend.continuousOn
  · simp
  · simp [map_sub]
  · simp [map_sub]
  · exact walkBetween_near_vertices E z D N hvertices hstep i j hi hj
  · exact walkBetween_near_vertices E z D N hvertices hstep i k hi hk

theorem sqDist_walk_determinant_le_differences (E : Finset Point) (z : ℕ → Point)
    (R N : ℕ) (hvertices : ∀ j ≤ N, z j ∈ E)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (i j k : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    ((z j - z i).1 * (z k - z i).2 - (z j - z i).2 * (z k - z i).1).natAbs ≤
      (pointDifferences E).card * (4 * (R + 1) + 1) ^ 2 :=
  walk_determinant_le_differences E z (R + 1) N hvertices
    (fun t _ => sqDist_walk_coordinate_steps z R hstep t) i j k hi hj hk

def walkVertexSet (z : ℕ → Point) (N : ℕ) : Finset Point :=
  (Finset.range (N + 1)).image z

theorem mem_walkVertexSet (z : ℕ → Point) (N i : ℕ) (hi : i ≤ N) :
    z i ∈ walkVertexSet z N :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem walkVertexSet_card (z : ℕ → Point) (N : ℕ)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) :
    (walkVertexSet z N).card = N + 1 := by
  rw [walkVertexSet, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  exact hinj i (by simpa using hi) j (by simpa using hj) he

/-- Subtracting one fixed vertex also covers the collinear/width-one branch. -/
theorem pointDifferences_card_ge (E : Finset Point) (hne : E.Nonempty) :
    E.card ≤ (pointDifferences E).card := by
  obtain ⟨w, hw⟩ := hne
  have hsubset : E.image (fun v => v - w) ⊆ pointDifferences E := by
    intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    exact (mem_pointDifferences E _).mpr ⟨v, hv, w, hw, rfl⟩
  have hinj : Function.Injective (fun v : Point => v - w) := by
    intro v u he
    exact sub_left_inj.mp he
  rw [← Finset.card_image_of_injective E hinj]
  exact Finset.card_le_card hsubset

/-- Canonical finite-prefix version in the determinant API used by Harper. -/
theorem prefix_walk_determinant_le_differences (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (i j k : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    (determinant (z j - z i) (z k - z i)).natAbs ≤
      (pointDifferences (walkVertexSet z N)).card * (4 * D + 1) ^ 2 :=
  walk_determinant_le_differences (walkVertexSet z N) z D N
    (mem_walkVertexSet z N) hstep i j k hi hj hk

theorem prefix_differences_card_ge (z : ℕ → Point) (N : ℕ)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) :
    N + 1 ≤ (pointDifferences (walkVertexSet z N)).card := by
  rw [← walkVertexSet_card z N hinj]
  exact pointDifferences_card_ge _ ⟨z 0, mem_walkVertexSet z N 0 (Nat.zero_le _)⟩

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.coordinate_steps_real
#print axioms BinaryFormMoat.GeometryIntegration.segment_near_source
#print axioms BinaryFormMoat.GeometryIntegration.walkPath_range_near_vertex
#print axioms BinaryFormMoat.GeometryIntegration.walkBetween_near_vertices
#print axioms BinaryFormMoat.GeometryIntegration.walk_determinant_le_differences
#print axioms BinaryFormMoat.GeometryIntegration.sqDist_walk_determinant_le_differences
#print axioms BinaryFormMoat.GeometryIntegration.mem_walkVertexSet
#print axioms BinaryFormMoat.GeometryIntegration.walkVertexSet_card
#print axioms BinaryFormMoat.GeometryIntegration.pointDifferences_card_ge
#print axioms BinaryFormMoat.GeometryIntegration.prefix_walk_determinant_le_differences
#print axioms BinaryFormMoat.GeometryIntegration.prefix_differences_card_ge
