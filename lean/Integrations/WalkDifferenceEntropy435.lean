import Integrations.FairDifferenceEntropy435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

theorem walk_differences_nonempty (z : ℕ → Point) (N : ℕ) :
    (pointDifferences (walkVertexSet z N)).Nonempty := by
  obtain ⟨h⟩ := walkDifferences_nonempty z N
  exact ⟨h.val, h.property⟩

theorem log_prefixArea_le_log_differences (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) :
    Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ) ≤
      Real.log ((pointDifferences (walkVertexSet z N)).card : ℝ) := by
  have hH : (0 : ℝ) < (pointDifferences (walkVertexSet z N)).card := by
    exact_mod_cast (walk_differences_nonempty z N).card_pos
  have hC : (0 : ℝ) < (4 * D + 1 : ℕ) := by positivity
  have hA : (0 : ℝ) < prefixArea z N := by exact_mod_cast prefixArea_pos z N
  have hb : (prefixArea z N : ℝ) ≤
      (pointDifferences (walkVertexSet z N)).card * (4 * D + 1 : ℕ) ^ 2 := by
    exact_mod_cast prefixArea_le_differences z D N hstep hinj
  have hlog := Real.log_le_log hA hb
  rw [Real.log_mul hH.ne' (pow_ne_zero 2 hC.ne'), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- Observation cost is paid once after averaging projections. The geometric
log-area floor is derived from the actual finite self-avoiding walk. -/
theorem mean_uniform_walk_projection_condEntropy_area_ge {J Q O : Type*}
    [Fintype J] [Nonempty J] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    (F : J → Point → Q) (Z : J → WalkDifferences z N → O) (ε B : ℝ) (hε : ε ≤ 1)
    (herr : ((badProjectionIndices (pointDifferences (walkVertexSet z N)) F).card : ℝ) /
      Fintype.card J ≤ ε)
    (hobs : ∀ j, entropy (Z j) (uniformOn (Set.univ : Set (WalkDifferences z N))) ≤ B) :
    (1 - ε) * (Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ)) - B ≤
      (∑ j, condEntropy (fun h : WalkDifferences z N => F j h.val) (Z j)
        (uniformOn (Set.univ : Set (WalkDifferences z N)))) / Fintype.card J := by
  have h := mean_uniform_projection_condEntropy_ge _ (walk_differences_nonempty z N)
    F Z ε B herr hobs
  have hg := mul_le_mul_of_nonneg_left (log_prefixArea_le_log_differences z D N hstep hinj)
    (sub_nonneg.mpr hε)
  linarith

theorem differenceEndpoint_entropy_ge_prefixArea_half (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    {Q : Type*} [AddCommGroup Q] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (F : Point →+ Q)
    (hF : Set.InjOn F (pointDifferences (walkVertexSet z N) : Set Point)) :
    (Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ)) / 2 ≤
      entropy (fun s => F (z (differenceEndpointIndex z N s).val))
        (differenceEndpointSourceLaw z N) := by
  have hg := log_prefixArea_le_log_differences z D N hstep hinj
  have he := differenceEndpoint_entropy_ge_uniformDifference_half z N F hF
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.walk_differences_nonempty
#print axioms BinaryFormMoat.GeometryIntegration.log_prefixArea_le_log_differences
#print axioms BinaryFormMoat.GeometryIntegration.mean_uniform_walk_projection_condEntropy_area_ge
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpoint_entropy_ge_prefixArea_half
