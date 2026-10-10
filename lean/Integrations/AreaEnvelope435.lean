import Integrations.WalkInterpolation435

namespace BinaryFormMoat.GeometryIntegration

/-- An integral area parameter chosen for the needed output inequalities.
It avoids diameter maximization, rotated-height selection and disk area. -/
def prefixArea (z : ℕ → Point) (N : ℕ) : ℕ :=
  max (N + 1) ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).sup
    (fun jk => (determinant (z jk.1 - z 0) (z jk.2 - z 0)).natAbs))

theorem prefixArea_pos (z : ℕ → Point) (N : ℕ) : 0 < prefixArea z N :=
  (Nat.succ_pos N).trans_le (le_max_left _ _)

theorem prefixArea_det_le (z : ℕ → Point) (N i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    (determinant (z i - z 0) (z j - z 0)).natAbs ≤ prefixArea z N := by
  apply (Finset.le_sup (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1))
    (f := fun jk => (determinant (z jk.1 - z 0) (z jk.2 - z 0)).natAbs)
    (b := (i, j)) ?_).trans (le_max_right _ _)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega)⟩

theorem prefixArea_le_differences (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) :
    prefixArea z N ≤ (pointDifferences (walkVertexSet z N)).card * (4 * D + 1) ^ 2 := by
  apply max_le
  · have h := prefix_differences_card_ge z N hinj
    have hc : 1 ≤ (4 * D + 1) ^ 2 := by
      have hp : 0 < (4 * D + 1) ^ 2 := by positivity
      omega
    nlinarith
  · apply Finset.sup_le
    intro jk hjk
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hjk
    exact prefix_walk_determinant_le_differences z D N hstep 0 jk.1 jk.2
      (Nat.zero_le _) (by simpa using hi) (by simpa using hj)

theorem coordinate_prefix_natAbs_le (w : ℕ → ℤ) (D N : ℕ)
    (hstep : ∀ j < N, |w (j + 1) - w j| ≤ D) :
    ∀ j ≤ N, (w j - w 0).natAbs ≤ D * N := by
  have hb : ∀ j ≤ N, (w j - w 0).natAbs ≤ D * j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hs : (w (j + 1) - w j).natAbs ≤ D := by
          exact_mod_cast (show ((w (j + 1) - w j).natAbs : ℤ) ≤ D by
            simpa only [Int.natCast_natAbs] using hstep j (by omega))
        calc
          _ = ((w (j + 1) - w j) + (w j - w 0)).natAbs := by congr 1; ring
          _ ≤ (w (j + 1) - w j).natAbs + (w j - w 0).natAbs := Int.natAbs_add_le _ _
          _ ≤ D + D * j := Nat.add_le_add hs (ih (by omega))
          _ = D * (j + 1) := by ring
  exact fun j hj => (hb j hj).trans (Nat.mul_le_mul_left D hj)

theorem prefixArea_upper (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D) :
    prefixArea z N ≤ 2 * (D + 1) ^ 2 * (N + 1) ^ 2 := by
  have hx := coordinate_prefix_natAbs_le (fun j => (z j).1) D N
    (fun j hj => (hstep j hj).1)
  have hy := coordinate_prefix_natAbs_le (fun j => (z j).2) D N
    (fun j hj => (hstep j hj).2)
  apply max_le
  · calc
      N + 1 ≤ (N + 1) ^ 2 := by nlinarith
      _ = 1 * (N + 1) ^ 2 := by simp
      _ ≤ (2 * (D + 1) ^ 2) * (N + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by
          have hp : 0 < 2 * (D + 1) ^ 2 := by positivity
          omega)
  · apply Finset.sup_le
    intro jk hjk
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hjk
    have hi' : jk.1 ≤ N := by simpa using hi
    have hj' : jk.2 ≤ N := by simpa using hj
    have h := determinant_natAbs_le (z jk.1 - z 0) (z jk.2 - z 0) (D * N) (D * N)
      (hx _ hi') (hy _ hi') (hx _ hj') (hy _ hj')
    have hDN : D * N ≤ (D + 1) * (N + 1) := by nlinarith
    calc
      _ ≤ 2 * (D * N) * (D * N) := h
      _ ≤ 2 * ((D + 1) * (N + 1)) * ((D + 1) * (N + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hDN) hDN
      _ = _ := by ring

theorem determinant_sub_sub_natAbs_le (a b c d : Point) (M : ℕ)
    (hac : (determinant a c).natAbs ≤ M) (had : (determinant a d).natAbs ≤ M)
    (hbc : (determinant b c).natAbs ≤ M) (hbd : (determinant b d).natAbs ≤ M) :
    (determinant (a - b) (c - d)).natAbs ≤ 4 * M := by
  have he : determinant (a - b) (c - d) =
      (determinant a c - determinant a d) - (determinant b c - determinant b d) := by
    simp only [determinant, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [he]
  calc
    _ ≤ (determinant a c - determinant a d).natAbs +
        (determinant b c - determinant b d).natAbs := Int.natAbs_sub_le _ _
    _ ≤ ((determinant a c).natAbs + (determinant a d).natAbs) +
        ((determinant b c).natAbs + (determinant b d).natAbs) :=
      Nat.add_le_add (Int.natAbs_sub_le _ _) (Int.natAbs_sub_le _ _)
    _ ≤ (M + M) + (M + M) := Nat.add_le_add (Nat.add_le_add hac had) (Nat.add_le_add hbc hbd)
    _ = _ := by ring

theorem centered_pointDifferences_determinant_le (E : Finset Point) (c : Point) (M : ℕ)
    (hdet : ∀ u ∈ E, ∀ v ∈ E, (determinant (u - c) (v - c)).natAbs ≤ M) :
    ∀ h ∈ pointDifferences E, ∀ g ∈ pointDifferences E,
      (determinant h g).natAbs ≤ 4 * M := by
  intro h hh g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_pointDifferences E h).mp hh
  obtain ⟨d, hd, e, he, rfl⟩ := (mem_pointDifferences E g).mp hg
  have ht := determinant_sub_sub_natAbs_le (a - c) (b - c) (d - c) (e - c) M
    (hdet a ha d hd) (hdet a ha e he) (hdet b hb d hd) (hdet b hb e he)
  have hab : (a - c) - (b - c) = a - b := by abel
  have hde : (d - c) - (e - c) = d - e := by abel
  rwa [hab, hde] at ht

theorem prefix_difference_determinant_le (z : ℕ → Point) (N : ℕ) :
    ∀ h ∈ pointDifferences (walkVertexSet z N),
      ∀ g ∈ pointDifferences (walkVertexSet z N),
        (determinant h g).natAbs ≤ 4 * prefixArea z N := by
  apply centered_pointDifferences_determinant_le _ (z 0)
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  exact prefixArea_det_le z N i j (by simpa using hi) (by simpa using hj)

theorem prefix_second_difference_determinant_le (z : ℕ → Point) (N : ℕ) :
    ∀ h ∈ pointDifferences (pointDifferences (walkVertexSet z N)),
      ∀ g ∈ pointDifferences (pointDifferences (walkVertexSet z N)),
        (determinant h g).natAbs ≤ 16 * prefixArea z N := by
  have h := centered_pointDifferences_determinant_le
    (pointDifferences (walkVertexSet z N)) 0 (4 * prefixArea z N)
    (by simpa only [sub_zero] using prefix_difference_determinant_le z N)
  simpa only [← Nat.mul_assoc] using h

theorem prefix_second_difference_radius_le (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D) :
    ∀ h ∈ pointDifferences (pointDifferences (walkVertexSet z N)),
      max h.1.natAbs h.2.natAbs ≤ 4 * (D * N) := by
  have hx := coordinate_prefix_natAbs_le (fun j => (z j).1) D N
    (fun j hj => (hstep j hj).1)
  have hy := coordinate_prefix_natAbs_le (fun j => (z j).2) D N
    (fun j hj => (hstep j hj).2)
  have hd : ∀ h ∈ pointDifferences (walkVertexSet z N),
      h.1.natAbs ≤ 2 * (D * N) ∧ h.2.natAbs ≤ 2 * (D * N) := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_pointDifferences _ h).mp hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hi' : i ≤ N := by simpa using hi
    have hj' : j ≤ N := by simpa using hj
    constructor
    · have h := Int.natAbs_sub_le ((z i).1 - (z 0).1) ((z j).1 - (z 0).1)
      have he : ((z i).1 - (z 0).1) - ((z j).1 - (z 0).1) = (z i).1 - (z j).1 := by ring
      rw [he] at h
      change ((z i).1 - (z j).1).natAbs ≤ _
      nlinarith [hx i hi', hx j hj']
    · have h := Int.natAbs_sub_le ((z i).2 - (z 0).2) ((z j).2 - (z 0).2)
      have he : ((z i).2 - (z 0).2) - ((z j).2 - (z 0).2) = (z i).2 - (z j).2 := by ring
      rw [he] at h
      change ((z i).2 - (z j).2).natAbs ≤ _
      nlinarith [hy i hi', hy j hj']
  intro h hh
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_pointDifferences _ h).mp hh
  obtain ⟨ha1, ha2⟩ := hd a ha
  obtain ⟨hb1, hb2⟩ := hd b hb
  apply max_le
  · change (a.1 - b.1).natAbs ≤ _
    have h := Int.natAbs_sub_le a.1 b.1
    omega
  · change (a.2 - b.2).natAbs ≤ _
    have h := Int.natAbs_sub_le a.2 b.2
    omega

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.prefixArea_pos
#print axioms BinaryFormMoat.GeometryIntegration.prefixArea_det_le
#print axioms BinaryFormMoat.GeometryIntegration.prefixArea_le_differences
#print axioms BinaryFormMoat.GeometryIntegration.coordinate_prefix_natAbs_le
#print axioms BinaryFormMoat.GeometryIntegration.prefixArea_upper
#print axioms BinaryFormMoat.GeometryIntegration.determinant_sub_sub_natAbs_le
#print axioms BinaryFormMoat.GeometryIntegration.centered_pointDifferences_determinant_le
#print axioms BinaryFormMoat.GeometryIntegration.prefix_difference_determinant_le
#print axioms BinaryFormMoat.GeometryIntegration.prefix_second_difference_determinant_le
#print axioms BinaryFormMoat.GeometryIntegration.prefix_second_difference_radius_le
