import Integrations.RealLattice435
import Integrations.PeriodicDeviation435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- Reducing the Brouwer parameters modulo one leaves an INTEGER lattice
translate. The two paths have the actual endpoint directions a,b. -/
theorem path_difference_mod_lattice (a b : Point)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) (α γ : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : α 0 = γ 0) (ha : α 1 - α 0 = realPoint a)
    (hb : γ 1 - γ 0 = realPoint b) (k : Point) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ l ∈ pointLattice a b, α s - γ t = realPoint (k - l) := by
  obtain ⟨x, hx⟩ := path_perturbation_surjective (endpointEquiv a b hdet)
    α γ hα hγ (realPoint k)
  change endpointEquiv a b hdet x + pathDeviationPair α γ x = realPoint k at hx
  let s := Int.fract (x 0)
  let t := Int.fract (x 1)
  let m : ℤ := ⌊x 0⌋
  let n : ℤ := ⌊x 1⌋
  let l : Point := m • a - n • b
  have hl : realPoint l = (m : ℝ) • realPoint a - (n : ℝ) • realPoint b := by
    simp only [l, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]
  have he : endpointEquiv a b hdet x + pathDeviationPair α γ x =
      realPoint l + (α s - γ t) := by
    rw [endpointEquiv_apply, hl]
    simp only [pathDeviationPair, periodicExtension_eq_fract, pathDeviation, ha, hb]
    rw [hstart]
    ext i
    simp only [s, t, m, n, Int.fract, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨s, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
    t, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
    l, lattice_integer_translate a b m n, ?_⟩
  rw [map_sub]
  rw [he] at hx
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hx))

/-- Nearby vertices turn the real path surjection into a finite cover of
the integer quotient, with integral coordinate error at most 2D. -/
theorem path_differences_box_cover (E : Finset Point) (a b : Point) (D : ℕ)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) (α γ : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : α 0 = γ 0) (ha : α 1 - α 0 = realPoint a)
    (hb : γ 1 - γ 0 = realPoint b)
    (hnearα : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ E,
      ∀ i, |α s i - realPoint v i| ≤ (D : ℝ))
    (hnearγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ E,
      ∀ i, |γ t i - realPoint w i| ≤ (D : ℝ)) :
    ∀ k : Point, ∃ h ∈ pointDifferences E, ∃ e ∈ displacementBox (2 * D),
      (pointLattice a b).mkQ (h + e) = (pointLattice a b).mkQ k := by
  intro k
  obtain ⟨s, hs, t, ht, l, hl, he⟩ :=
    path_difference_mod_lattice a b hdet α γ hα hγ hstart ha hb k
  obtain ⟨v, hv, hvs⟩ := hnearα s hs
  obtain ⟨w, hw, hwt⟩ := hnearγ t ht
  rw [map_sub] at he
  let h := v - w
  let e := (k - l) - h
  have her : realPoint e = (α s - realPoint v) - (γ t - realPoint w) := by
    simp only [e, h, map_sub]
    rw [← he]
    abel
  have heb : ∀ i, |realPoint e i| ≤ (2 * D : ℕ) := by
    intro i
    rw [her]
    change |(α s i - realPoint v i) - (γ t i - realPoint w i)| ≤ _
    apply (abs_sub _ _).trans
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith [hvs i, hwt i]
  have hebox : e ∈ displacementBox (2 * D) := by
    apply (mem_displacementBox _ _).mpr
    constructor
    · have hx := heb 0
      change |(e.1 : ℝ)| ≤ ((2 * D : ℕ) : ℝ) at hx
      exact_mod_cast hx
    · have hy := heb 1
      change |(e.2 : ℝ)| ≤ ((2 * D : ℕ) : ℝ) at hy
      exact_mod_cast hy
  refine ⟨h, (mem_pointDifferences E h).mpr ⟨v, hv, w, hw, rfl⟩, e, hebox, ?_⟩
  have hlzero : (pointLattice a b).mkQ l = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hl
  have hhe : h + e = k - l := by dsimp [e]; abel
  rw [hhe, map_sub, hlzero, sub_zero]

/-- The cover is derived from the paths and nearby vertices, not assumed. -/
theorem determinant_le_path_differences (E : Finset Point) (a b : Point) (D : ℕ)
    (hdet : a.1 * b.2 - a.2 * b.1 ≠ 0) (α γ : ℝ → RealPlane)
    (hα : ContinuousOn α (Set.Icc 0 1)) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : α 0 = γ 0) (ha : α 1 - α 0 = realPoint a)
    (hb : γ 1 - γ 0 = realPoint b)
    (hnearα : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ E,
      ∀ i, |α s i - realPoint v i| ≤ (D : ℝ))
    (hnearγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ E,
      ∀ i, |γ t i - realPoint w i| ≤ (D : ℝ)) :
    (a.1 * b.2 - a.2 * b.1).natAbs ≤
      (pointDifferences E).card * (4 * D + 1) ^ 2 :=
  determinant_le_differences_of_cover E a b D hdet
    (path_differences_box_cover E a b D hdet α γ hα hγ hstart ha hb hnearα hnearγ)

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.path_difference_mod_lattice
#print axioms BinaryFormMoat.GeometryIntegration.path_differences_box_cover
#print axioms BinaryFormMoat.GeometryIntegration.determinant_le_path_differences
