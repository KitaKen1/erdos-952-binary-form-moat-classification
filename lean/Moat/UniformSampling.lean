import Moat.FiniteSampling
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory

namespace BinaryFormMoat

/-- Finite counting probabilities agree with the uniform probability measure. -/
theorem uniformOn_real_event {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (S : Finset K) (Q : K → Prop) [DecidablePred Q] :
    (uniformOn (S : Set K)).real {x | Q x} =
      ((S.filter Q).card : ℝ) / S.card := by
  classical
  have he : {x | Q x} = ((Finset.univ.filter Q : Finset K) : Set K) := by ext; simp
  rw [measureReal_def, he, uniformOn_apply_finset]
  have hi : S ∩ Finset.univ.filter Q = S.filter Q := by ext; simp
  simp [hi]

/-- Integration against the uniform law is exactly the finite average used
in the preceding root-selection lemmas. -/
theorem integral_uniformOn_finset {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (S : Finset K) (f : K → ℝ) :
    (∫ x, f x ∂uniformOn (S : Set K)) = (∑ x ∈ S, f x) / S.card := by
  classical
  rw [uniformOn, ProbabilityTheory.cond, integral_smul_measure,
    setIntegral_finset S Integrable.of_finite]
  simp [measureReal_def, div_eq_mul_inv, mul_comm]

/-- A dependent finite box carries the product of the uniform coordinate laws.
The coordinate alphabets may have different types, such as ZMod p for each p. -/
theorem uniformOn_piFinset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (S : ∀ i, Finset (K i)) :
    uniformOn (Fintype.piFinset S : Set (∀ i, K i)) =
      Measure.pi (fun i => uniformOn (S i : Set (K i))) := by
  classical
  refine (Measure.pi_eq fun t _ => ?_).symm
  lift t to ∀ i, Finset (K i) using by simp [Set.toFinite]
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne_top]

/-- Coordinate functions of independently and uniformly selected roots really
are independent under the same measure as the finite counting calculation. -/
theorem iIndepFun_uniformOn_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → Type*} [∀ i, Fintype (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, MeasurableSingletonClass (K i)] (S : ∀ i, Finset (K i))
    (hS : ∀ i, (S i).Nonempty) (g : ∀ i, K i → ℝ) :
    iIndepFun (fun i σ => g i (σ i))
      (uniformOn (Fintype.piFinset S : Set (∀ i, K i))) := by
  let : ∀ i, IsProbabilityMeasure (uniformOn (S i : Set (K i))) :=
    fun i => isProbabilityMeasure_uniformOn (S i).finite_toSet (hS i)
  rw [uniformOn_piFinset]
  exact iIndepFun_pi fun _ => Measurable.aemeasurable (by measurability)

end BinaryFormMoat
