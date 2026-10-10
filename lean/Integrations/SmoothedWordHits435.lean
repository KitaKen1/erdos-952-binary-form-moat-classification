import Integrations.ShortWordHits435
import Integrations.TerminalSchedule435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section FiniteSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]

/-- A base hit floor persists at every offset of the actual terminal word. -/
theorem smoothedTimeLaw_word_offset_hit_floor {G : Type*} (V : ℕ → G) (c : G)
    (L : ℕ) (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b N).real {t | V t = c})
    (i : Fin L) :
    δ - (L : ℝ) / N ≤
      (smoothedTimeLaw μ b N).real (wordHitEvent V id (fun _ => c) i) := by
  have hs := smoothedTimeLaw_shift_event_bound μ b N {t | V t = c} i.val
  change |(smoothedTimeLaw μ b N).real (wordHitEvent V id (fun _ => c) i) -
    (smoothedTimeLaw μ b N).real {t | V t = c}| ≤ (i.val : ℝ) / N at hs
  have hi : (i.val : ℝ) / N ≤ (L : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast i.isLt.le) (Nat.cast_nonneg N)
  have hl := (abs_le.mp hs).1
  linarith

theorem smoothedTimeLaw_word_hit_floor {G : Type*} (V : ℕ → G) (c : G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b N).real {t | V t = c}) :
    (L : ℝ) * (δ - (L : ℝ) / N) ≤
      (smoothedTimeLaw μ b N).real (wordHitSet V id (fun _ => c) L) := by
  exact wordHit_probability_ge_length_mul (smoothedTimeLaw μ b N) V id (fun _ => c)
    L hinj _ (smoothedTimeLaw_word_offset_hit_floor μ b N V c L δ hδ)

theorem smoothedTimeLaw_word_hit_half_floor {G : Type*} (V : ℕ → G) (c : G) (L : ℕ)
    (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b N).real {t | V t = c})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 ≤
      (smoothedTimeLaw μ b N).real (wordHitSet V id (fun _ => c) L) := by
  calc
    _ = (L : ℝ) * (δ / 2) := by ring
    _ ≤ (L : ℝ) * (δ - (L : ℝ) / N) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg L)
    _ ≤ _ := smoothedTimeLaw_word_hit_floor μ b N V c L hinj δ hδ

theorem smoothedTimeLaw_root_word_hit_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b N).real {t | rootResidueHom p ρ (z t) = c}) :
    (L : ℝ) * (δ - (L : ℝ) / N) ≤ (smoothedTimeLaw μ b N).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) := by
  exact smoothedTimeLaw_word_hit_floor μ b N _ c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall) δ hδ

theorem smoothedTimeLaw_root_word_hit_half_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b N).real {t | rootResidueHom p ρ (z t) = c})
    (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 ≤ (smoothedTimeLaw μ b N).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) := by
  exact smoothedTimeLaw_word_hit_half_floor μ b N _ c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall)
    δ hδ herr

/-- The manuscript's per-package scale follows from an actual singleton
floor and an explicit smoothing quota; the floor itself is not assumed proved. -/
theorem smoothedTimeLaw_root_word_hit_prime_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ : ℝ) (hτ : τ / p ≤ (smoothedTimeLaw μ b N).real {t | rootResidueHom p ρ (z t) = c})
    (herr : (L : ℝ) / N ≤ (τ / p) / 2) :
    (L : ℝ) * (τ / p) / 2 ≤ (smoothedTimeLaw μ b N).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) :=
  smoothedTimeLaw_root_word_hit_half_floor μ b N f hf hd p ρ hρ z hz R hstep c L hsmall
    (τ / p) hτ herr

/-- Apply the same floor under the exact positive earlier-checkpoint fiber. -/
theorem smoothedTimeLaw_cond_root_word_hit_half_floor {A : Type*}
    (V : Ω → A) (v : A) (hv : μ (V ⁻¹' {v}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N).real
      {t | rootResidueHom p ρ (z t) = c}) (herr : (L : ℝ) / N ≤ δ / 2) :
    (L : ℝ) * δ / 2 ≤ (smoothedTimeLaw (μ[|V ⁻¹' {v}]) b N).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) := by
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact smoothedTimeLaw_root_word_hit_half_floor (μ[|V ⁻¹' {v}]) b N f hf hd p ρ hρ
    z hz R hstep c L hsmall δ hδ herr

end FiniteSource

section CeilingSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)

theorem smoothedTimeLaw_ceiling_word_hit_floor {G : Type*} (V : ℕ → G) (c : G)
    (L : ℕ) (hinj : ∀ t, Function.Injective (fun i : Fin L => V (t + i)))
    (T : ℝ) (hT : 0 < T) (hL : (L : ℝ) ≤ T)
    (δ : ℝ) (hδ : δ ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real {t | V t = c}) :
    (L : ℝ) * (δ - 1 / T ^ 9) ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real
      (wordHitSet V id (fun _ => c) L) := by
  have : NeZero (terminalSmoothingLength T) := ⟨(terminalSmoothingLength_pos T).ne'⟩
  apply wordHit_probability_ge_length_mul _ V id (fun _ => c) L hinj
  intro i
  have hi : (i.val : ℝ) ≤ T := (by exact_mod_cast i.isLt.le : (i.val : ℝ) ≤ L).trans hL
  have hs := smoothedTimeLaw_ceiling_source_bound μ b {t | V t = c} i.val T hT hi
  change |(smoothedTimeLaw μ b (terminalSmoothingLength T)).real (wordHitEvent V id (fun _ => c) i) -
    (smoothedTimeLaw μ b (terminalSmoothingLength T)).real {t | V t = c}| ≤ 1 / T ^ 9 at hs
  have hl := (abs_le.mp hs).1
  linarith

theorem smoothedTimeLaw_ceiling_root_word_hit_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (T : ℝ) (hT : 0 < T) (hL : (L : ℝ) ≤ T) (δ : ℝ)
    (hδ : δ ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real
      {t | rootResidueHom p ρ (z t) = c}) :
    (L : ℝ) * (δ - 1 / T ^ 9) ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) := by
  exact smoothedTimeLaw_ceiling_word_hit_floor μ b _ c L
    (fun t => short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall)
    T hT hL δ hδ

theorem smoothedTimeLaw_ceiling_root_word_hit_prime_floor (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (c : ZMod p) (L : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (T : ℝ) (hT : 0 < T) (hL : (L : ℝ) ≤ T) (τ : ℝ)
    (hτ : τ / p ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real
      {t | rootResidueHom p ρ (z t) = c}) (herr : 1 / T ^ 9 ≤ (τ / p) / 2) :
    (L : ℝ) * (τ / p) / 2 ≤ (smoothedTimeLaw μ b (terminalSmoothingLength T)).real
      (wordHitSet (fun t => rootResidueHom p ρ (z t)) id (fun _ => c) L) := by
  calc
    _ = (L : ℝ) * ((τ / p) / 2) := by ring
    _ ≤ (L : ℝ) * (τ / p - 1 / T ^ 9) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg L)
    _ ≤ _ := smoothedTimeLaw_ceiling_root_word_hit_floor μ b f hf hd p ρ hρ z hz R hstep
      c L hsmall T hT hL (τ / p) hτ

end CeilingSource
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_offset_hit_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_hit_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_hit_half_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_hit_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_hit_half_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_root_word_hit_prime_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_cond_root_word_hit_half_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_ceiling_word_hit_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_ceiling_root_word_hit_floor
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_ceiling_root_word_hit_prime_floor
