import Integrations.RootResidues435
import Moat.IrreducibleValues

namespace BinaryFormMoat.EntropyIntegration

/-- A nonzero homogenized value cannot be a positive multiple of a larger
modulus. No primitivity or shortest-vector theorem is required. -/
theorem rootResidueHom_ne_zero_of_small_value (f : Polynomial ℤ) (n : ℕ)
    (hn : f.natDegree ≤ n) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (v : Point)
    (hv : value (f.homogenize n) v ≠ 0)
    (hsmall : (value (f.homogenize n) v).natAbs < p) :
    rootResidueHom p ρ v ≠ 0 := by
  intro hzero
  have hdiv := rootResidueHom_zero_dvd_value f n hn p ρ hρ v hzero
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hdiv)) hsmall

theorem rootResidueHom_ne_zero_of_small_box (f : Polynomial ℤ) (n : ℕ)
    (hn : f.natDegree ≤ n) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (v : Point)
    (hv : value (f.homogenize n) v ≠ 0) (A : ℕ)
    (hx : v.1.natAbs ≤ A) (hy : v.2.natAbs ≤ A)
    (hsmall : coefficientBound f n * A ^ n < p) :
    rootResidueHom p ρ v ≠ 0 := by
  exact rootResidueHom_ne_zero_of_small_value f n hn p ρ hρ v hv
    ((homogenized_value_growth f n v A hx hy).trans_lt hsmall)

theorem irreducible_rootResidueHom_ne_zero_of_small_box (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0) (v : Point) (hv : v ≠ 0)
    (A : ℕ) (hx : v.1.natAbs ≤ A) (hy : v.2.natAbs ≤ A)
    (hsmall : coefficientBound f f.natDegree * A ^ f.natDegree < p) :
    rootResidueHom p ρ v ≠ 0 := by
  have hcoords : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_cases hx : v.1 = 0
    · right
      intro hy
      exact hv (Prod.ext hx hy)
    · exact Or.inl hx
  exact rootResidueHom_ne_zero_of_small_box f f.natDegree le_rfl p ρ hρ v
    (irreducible_homogenization_value_ne_zero f hf hd v hcoords) A hx hy hsmall

/-- Differences of two positions within the same finite word have bounded
coordinates in either time order. -/
theorem walk_word_difference_natAbs_le (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (L t : ℕ) (i j : Fin L) :
    ((z (t + i) - z (t + j)).1).natAbs ≤ (R + 1) * L ∧
      ((z (t + i) - z (t + j)).2).natAbs ≤ (R + 1) * L := by
  have hc := sqDist_walk_coordinate_steps z R hstep
  have hb : |(z (t + i) - z (t + j)).1| ≤ ((R + 1) * L : ℕ) ∧
      |(z (t + i) - z (t + j)).2| ≤ ((R + 1) * L : ℕ) := by
    rcases le_total i.val j.val with hij | hji
    · have hm := (mem_displacementBox _ _).mp
        (walk_displacement_mem z (R + 1) hc L (t + i) (t + j) (by omega) (by omega))
      simpa only [Prod.fst_sub, Prod.snd_sub, abs_sub_comm] using hm
    · exact (mem_displacementBox _ _).mp
        (walk_displacement_mem z (R + 1) hc L (t + j) (t + i) (by omega) (by omega))
  constructor
  · exact_mod_cast (show (((z (t + i) - z (t + j)).1).natAbs : ℤ) ≤
      ((R + 1) * L : ℕ) by simpa only [Int.natCast_natAbs] using hb.1)
  · exact_mod_cast (show (((z (t + i) - z (t + j)).2).natAbs : ℤ) ≤
      ((R + 1) * L : ℕ) by simpa only [Int.natCast_natAbs] using hb.2)

/-- Degree-dependent short-word injectivity, replacing the Gaussian
norm-p shortest-vector argument by integer polynomial growth. -/
theorem short_word_rootResidues_injective (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (L t : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p) :
    Function.Injective (fun i : Fin L => rootResidueHom p ρ (z (t + i))) := by
  intro i j h
  change rootResidueHom p ρ (z (t + i)) = rootResidueHom p ρ (z (t + j)) at h
  by_contra hij
  have hne : z (t + i) - z (t + j) ≠ 0 := by
    intro hzero
    have ht := hz (sub_eq_zero.mp hzero)
    exact hij (Fin.ext (by omega))
  have hb := walk_word_difference_natAbs_le z R hstep L t i j
  have hr := irreducible_rootResidueHom_ne_zero_of_small_box f hf hd p ρ hρ
    (z (t + i) - z (t + j)) hne ((R + 1) * L) hb.1 hb.2 hsmall
  exact hr (by rw [map_sub, h, sub_self])

theorem short_word_displacement_rootResidues_injective (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (L t : ℕ) (a : Point)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p) :
    Function.Injective (fun i : Fin L => rootResidueHom p ρ (z (t + i) - a)) := by
  intro i j h
  apply short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall
  have hh := congrArg (fun v => v + rootResidueHom p ρ a) h
  simpa only [map_sub, sub_add_cancel] using hh

theorem short_word_length_le_modulus (f : Polynomial ℤ)
    (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (p : ℕ) [NeZero p] (ρ : ZMod p)
    (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (L t : ℕ)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p) :
    L ≤ p := by
  simpa only [Fintype.card_fin, ZMod.card] using Fintype.card_le_of_injective _
    (short_word_rootResidues_injective f hf hd p ρ hρ z hz R hstep L t hsmall)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_ne_zero_of_small_value
#print axioms BinaryFormMoat.EntropyIntegration.rootResidueHom_ne_zero_of_small_box
#print axioms BinaryFormMoat.EntropyIntegration.irreducible_rootResidueHom_ne_zero_of_small_box
#print axioms BinaryFormMoat.EntropyIntegration.walk_word_difference_natAbs_le
#print axioms BinaryFormMoat.EntropyIntegration.short_word_rootResidues_injective
#print axioms BinaryFormMoat.EntropyIntegration.short_word_displacement_rootResidues_injective
#print axioms BinaryFormMoat.EntropyIntegration.short_word_length_le_modulus
