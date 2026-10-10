import Integrations.PackageInformation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section FiniteVariables
variable {Ω C K U D : Type*} [MeasurableSpace Ω]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Preserve conditional information through the entire original triple law. -/
theorem condMutualInfo_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : Ω → C) (Y : Ω → K) (Z : Ω → U)
    (X' : Ω' → C) (Y' : Ω' → K) (Z' : Ω' → U)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, (Y ω, Z ω)))
      (fun ω => (X' ω, (Y' ω, Z' ω))) μ ν) :
    condMutualInfo X Y Z μ = condMutualInfo X' Y' Z' ν := by
  have hp := h.comp (measurable_of_finite (fun v : C × (K × U) => (v.1, v.2.2)))
  rw [condMutualInfo_eq' hX hY hZ, condMutualInfo_eq' hX' hY' hZ',
    IdentDistrib.condEntropy_eq hX hZ hX' hZ' hp,
    IdentDistrib.condEntropy_eq hX (hY.prodMk hZ) hX' (hY'.prodMk hZ') h]

theorem condEntropy_le_add_observation_entropy (X : Ω → C) (Z : Ω → U) (S : Ω → D)
    (hX : Measurable X) (hZ : Measurable Z) (hS : Measurable S) :
    condEntropy X Z μ ≤ entropy S μ + condEntropy X (fun ω => (S ω, Z ω)) μ := by
  have hfirst := cond_chain_rule' μ hX hS hZ
  have hsecond := cond_chain_rule μ hX hS hZ
  have hn := condEntropy_nonneg S (fun ω => (X ω, Z ω)) μ
  have he := condEntropy_le_entropy μ hS hZ
  linarith

/-- Tuple reordering changes no conditioning information. -/
theorem condEntropy_condition_rotate (X : Ω → C) (S : Ω → D) (Y : Ω → K) (Z : Ω → U)
    (hX : Measurable X) (hS : Measurable S) (hY : Measurable Y) (hZ : Measurable Z) :
    condEntropy X (fun ω => ((S ω, Y ω), Z ω)) μ =
      condEntropy X (fun ω => (Y ω, (S ω, Z ω))) μ := by
  let f := fun v : (D × K) × U => (v.1.2, (v.1.1, v.2))
  have hf : Function.Injective f := by
    intro a b hab
    exact Prod.ext (Prod.ext (congrArg (fun v => v.2.1) hab) (congrArg Prod.fst hab))
      (congrArg (fun v => v.2.2) hab)
  exact (condEntropy_of_injective' μ hX ((hS.prodMk hY).prodMk hZ) f hf
    (hY.prodMk (hS.prodMk hZ))).symm

theorem condMutualInfo_pair_chain (X : Ω → C) (S : Ω → D) (Y : Ω → K) (Z : Ω → U)
    (hX : Measurable X) (hS : Measurable S) (hY : Measurable Y) (hZ : Measurable Z) :
    condMutualInfo X (fun ω => (S ω, Y ω)) Z μ =
      condMutualInfo X S Z μ + condMutualInfo X Y (fun ω => (S ω, Z ω)) μ := by
  rw [condMutualInfo_eq' hX (hS.prodMk hY) hZ, condMutualInfo_eq' hX hS hZ,
    condMutualInfo_eq' hX hY (hS.prodMk hZ),
    condEntropy_condition_rotate μ X S Y Z hX hS hY hZ]
  ring

theorem condMutualInfo_le_right_entropy (X : Ω → C) (Y : Ω → K) (Z : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    condMutualInfo X Y Z μ ≤ entropy Y μ := by
  rw [condMutualInfo_comm hX hY, condMutualInfo_eq' hY hX hZ]
  have h := condEntropy_le_entropy μ hY hZ
  have hn := condEntropy_nonneg Y (fun ω => (X ω, Z ω)) μ
  linarith

/-- Removing conditioning costs at most the entropy of the removed datum,
without any independence premise. -/
theorem condMutualInfo_add_conditioning_le (X : Ω → C) (Y : Ω → K) (Z : Ω → U)
    (S : Ω → D) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hS : Measurable S) :
    condMutualInfo X Y (fun ω => (S ω, Z ω)) μ ≤
      condMutualInfo X Y Z μ + entropy S μ := by
  have h₁ := condMutualInfo_pair_chain μ X S Y Z hX hS hY hZ
  have h₂ := condMutualInfo_pair_chain μ X Y S Z hX hY hS hZ
  have hb := condMutualInfo_le_right_entropy μ X S (fun ω => (Y ω, Z ω))
    hX hS (hY.prodMk hZ)
  have hn := condMutualInfo_nonneg hX hS (Z := Z) (μ := μ)
  have hs := condMutualInfo_of_inj_map (hS.prodMk hY) hX hZ
    (fun _ v => Prod.swap v) (fun _ => Prod.swap_injective) (μ := μ)
  change condMutualInfo (fun ω => (Y ω, S ω)) X Z μ =
    condMutualInfo (fun ω => (S ω, Y ω)) X Z μ at hs
  rw [condMutualInfo_comm (hY.prodMk hS) hX, condMutualInfo_comm (hS.prodMk hY) hX] at hs
  linarith

variable [AddCommGroup C] [AddCommGroup U]

/-- Given the full displacement, both target and prior residues are
translated bijectively. Dependence of all variables is allowed. -/
theorem condMutualInfo_additive_translation_given_displacement
    (X : Ω → C) (W : Ω → K) (O : Ω → U) (S : Ω → D) (φ : D → C) (ψ : D → U)
    (hX : Measurable X) (hW : Measurable W) (hO : Measurable O) (hS : Measurable S) :
    condMutualInfo (fun ω => X ω + φ (S ω)) W
      (fun ω => (S ω, O ω + ψ (S ω))) μ =
    condMutualInfo X W (fun ω => (S ω, O ω)) μ := by
  have hX' := hX.add ((measurable_of_finite φ).comp hS)
  have hx := condMutualInfo_of_inj_map hX hW (hS.prodMk hO)
    (fun v x => x + φ v.1) (fun _ _ _ h => add_right_cancel h) (μ := μ)
  let f := fun v : D × U => (v.1, v.2 + ψ v.1)
  have hf : Function.Injective f := by
    rintro ⟨s, o⟩ ⟨t, p⟩ h
    have hs : s = t := congrArg Prod.fst h
    subst t
    exact Prod.ext rfl (add_right_cancel (congrArg Prod.snd h))
  have hc := condMutualInfo_of_inj hX' hW (hS.prodMk hO) μ hf
  exact hc.trans hx

/-- There are exactly two displacement costs: including S in the package,
then removing S from the translated conditioning observation. -/
theorem condMutualInfo_additive_transport (X : Ω → C) (W : Ω → K) (O : Ω → U)
    (S : Ω → D) (φ : D → C) (ψ : D → U)
    (hX : Measurable X) (hW : Measurable W) (hO : Measurable O) (hS : Measurable S) :
    condMutualInfo X (fun ω => (S ω, W ω)) O μ ≤
      condMutualInfo (fun ω => X ω + φ (S ω)) W (fun ω => O ω + ψ (S ω)) μ +
        2 * entropy S μ := by
  have hc := condMutualInfo_pair_chain μ X S W O hX hS hW hO
  have hb := condMutualInfo_le_right_entropy μ X S O hX hS hO
  have ht := condMutualInfo_additive_translation_given_displacement μ X W O S φ ψ
    hX hW hO hS
  have hr := condMutualInfo_add_conditioning_le μ (fun ω => X ω + φ (S ω)) W
    (fun ω => O ω + ψ (S ω)) S (hX.add ((measurable_of_finite φ).comp hS)) hW
    (hO.add ((measurable_of_finite ψ).comp hS)) hS
  linarith

end FiniteVariables
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_eq_of_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_add_observation_entropy
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_condition_rotate
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_pair_chain
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_le_right_entropy
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_add_conditioning_le
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_additive_translation_given_displacement
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_additive_transport
