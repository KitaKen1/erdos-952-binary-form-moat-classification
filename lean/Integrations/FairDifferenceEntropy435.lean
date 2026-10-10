import Integrations.DifferenceEndpoint435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

theorem integral_eq_probability_of_eq {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [DecidableEq Q]
    (μ : Measure Ω) (X : Ω → Q) (hX : Measurable X) (q : Q) :
    (∫ ω, if X ω = q then (1 : ℝ) else 0 ∂μ) = (μ.map X).real {q} := by
  classical
  rw [map_measureReal_apply hX (MeasurableSet.singleton q)]
  have he : (fun ω => if X ω = q then (1 : ℝ) else 0) =
      (X ⁻¹' {q}).indicator 1 := by
    funext ω
    by_cases h : X ω = q <;> simp [h]
  rw [he, integral_indicator_one (hX (MeasurableSet.singleton q))]

/-- Concavity at the actual singleton probabilities. The supplied law
identity will be derived below from the fair endpoint construction. -/
theorem finite_entropy_ge_half_of_singleton_average {Ω Ξ Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (V : Ω → Q) (X Y : Ξ → Q)
    (hmix : ∀ q, (μ.map V).real {q} = ((ν.map X).real {q} + (ν.map Y).real {q}) / 2) :
    (entropy X ν + entropy Y ν) / 2 ≤ entropy V μ := by
  classical
  simp_rw [entropy_eq_sum, tsum_fintype]
  calc
    _ = ∑ q, (Real.negMulLog ((ν.map X).real {q}) +
        Real.negMulLog ((ν.map Y).real {q})) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      rw [hmix q]
      have hc := Real.concaveOn_negMulLog.2
        (show (ν.map X).real {q} ∈ Set.Ici (0 : ℝ) from ENNReal.toReal_nonneg)
        (show (ν.map Y).real {q} ∈ Set.Ici (0 : ℝ) from ENNReal.toReal_nonneg)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
      have hh (a b : ℝ) : (1 / 2) * a + (1 / 2) * b = (a + b) / 2 := by ring
      simpa only [smul_eq_mul, hh] using hc

theorem differenceEndpoint_singleton_average (z : ℕ → Point) (N : ℕ)
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] (F : Point → Q) (q : Q) :
    ((differenceEndpointSourceLaw z N).map
      (fun s => F (z (differenceEndpointIndex z N s).val))).real {q} =
      (((uniformOn (Set.univ : Set (WalkDifferences z N))).map
        (fun h => F (z (walkDifferenceTimes z N h).1.val))).real {q} +
       ((uniformOn (Set.univ : Set (WalkDifferences z N))).map
        (fun h => F (z (walkDifferenceTimes z N h).2.val))).real {q}) / 2 := by
  classical
  have h := differenceEndpointSourceLaw_integral z N (fun x => if F x = q then 1 else 0)
  rw [integral_eq_probability_of_eq _ _ (measurable_of_finite _) q,
    integral_eq_probability_of_eq _ _ (measurable_of_finite _) q,
    integral_eq_probability_of_eq _ _ (measurable_of_finite _) q] at h
  exact h

/-- Fair endpoint mixing does not lose log(2) in the entropy lower bound. -/
theorem differenceEndpoint_entropy_ge_half (z : ℕ → Point) (N : ℕ)
    {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q] (F : Point → Q) :
    (entropy (fun h : WalkDifferences z N => F (z (walkDifferenceTimes z N h).1.val))
        (uniformOn (Set.univ : Set (WalkDifferences z N))) +
     entropy (fun h : WalkDifferences z N => F (z (walkDifferenceTimes z N h).2.val))
        (uniformOn (Set.univ : Set (WalkDifferences z N)))) / 2 ≤
      entropy (fun s => F (z (differenceEndpointIndex z N s).val))
        (differenceEndpointSourceLaw z N) := by
  apply finite_entropy_ge_half_of_singleton_average
  exact differenceEndpoint_singleton_average z N F

theorem differenceEndpoint_entropy_ge_uniformDifference_half (z : ℕ → Point) (N : ℕ)
    {Q : Type*} [AddCommGroup Q] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (F : Point →+ Q)
    (hinj : Set.InjOn F (pointDifferences (walkVertexSet z N) : Set Point)) :
    Real.log ((pointDifferences (walkVertexSet z N)).card : ℝ) / 2 ≤
      entropy (fun s => F (z (differenceEndpointIndex z N s).val))
        (differenceEndpointSourceLaw z N) := by
  classical
  let ν := uniformOn (Set.univ : Set (WalkDifferences z N))
  let X : WalkDifferences z N → Q := fun h => F (z (walkDifferenceTimes z N h).1.val)
  let Y : WalkDifferences z N → Q := fun h => F (z (walkDifferenceTimes z N h).2.val)
  have hd : (fun xy : Q × Q => xy.1 - xy.2) ∘ (fun h => (X h, Y h)) =
      (fun h : WalkDifferences z N => F h.val) := by
    funext h
    exact (F.map_sub _ _).symm.trans (congrArg F (walkDifferenceTimes_spec z N h))
  have hlo := entropy_comp_le ν (measurable_of_finite (fun h => (X h, Y h)))
    (fun xy : Q × Q => xy.1 - xy.2)
  rw [hd] at hlo
  have hne : (pointDifferences (walkVertexSet z N)).Nonempty := by
    exact ⟨0, (mem_pointDifferences _ _).mpr ⟨z 0, mem_walkVertexSet z N 0 (Nat.zero_le _),
      z 0, mem_walkVertexSet z N 0 (Nat.zero_le _), sub_self _⟩⟩
  rw [uniform_subtype_projection_entropy _ hne F hinj] at hlo
  have hpair := entropy_pair_le_add (measurable_of_finite X) (measurable_of_finite Y) ν
  have hmix := differenceEndpoint_entropy_ge_half z N (F : Point → Q)
  change (entropy X ν + entropy Y ν) / 2 ≤ _ at hmix
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.integral_eq_probability_of_eq
#print axioms BinaryFormMoat.GeometryIntegration.finite_entropy_ge_half_of_singleton_average
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpoint_singleton_average
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpoint_entropy_ge_half
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpoint_entropy_ge_uniformDifference_half
