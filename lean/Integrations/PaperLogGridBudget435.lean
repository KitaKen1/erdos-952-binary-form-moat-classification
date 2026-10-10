import Integrations.PaperLogGridWindows435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter

theorem tendsto_paperScheduleX (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (paperScheduleX d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (paperScheduleBase_gt_one d hd)

/-- ONE threshold makes every growing upper-half window wide enough.
The proof uses the actual half-window exponential lower envelope. -/
theorem paperLogGrid_uniform_wide (d B : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      40 * Real.log B ≤ paperScheduleX d m := by
  have ha : 0 < Real.log (paperScheduleBase d) / 2 :=
    div_pos (Real.log_pos (paperScheduleBase_gt_one d hd)) (by norm_num)
  have hg := Real.tendsto_exp_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop ha)
  obtain ⟨M0, hM0⟩ := (hg.eventually_ge_atTop (40 * Real.log B)).exists_forall_of_atTop
  refine ⟨M0, ?_⟩
  intro M hM m hm
  exact (hM0 M hM).trans ((paperScheduleX_half_lower d M hd).trans (paperScheduleX_mono d hd hm))

/-- Explicit linear lower bound on the ACTUAL finite reciprocal-log sum.
No assumed abundance of grid points and no infinite sum is used. -/
theorem paperGeometricLogBudget_lower (d M B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B)
    (hwide : ∀ m ∈ Finset.Icc ((M + 1) / 2) M, 40 * Real.log B ≤ paperScheduleX d m) :
    (M : ℝ) / (84 * Real.log B) ≤ paperGeometricLogBudget d M B := by
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  let W := Finset.Icc ((M + 1) / 2) M
  have hcardNat : M ≤ 2 * W.card := by dsimp [W]; rw [Nat.card_Icc]; omega
  have hcard : (M : ℝ) / 2 ≤ (W.card : ℝ) := by
    have h : (M : ℝ) ≤ 2 * (W.card : ℝ) := by exact_mod_cast hcardNat
    linarith
  rw [paperGeometricLogBudget_eq_sum_windows d M B hd hB]
  calc
    _ = ((M : ℝ) / 2) / (42 * Real.log B) := by ring
    _ ≤ (W.card : ℝ) / (42 * Real.log B) := div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ _m ∈ W, 1 / (42 * Real.log B) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun m hm => logGridWindow_reciprocal_lower _ _ hh (hwide m hm)

theorem paperGeometricLogBudget_eventually_lower (d B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    ∀ᶠ M : ℕ in atTop, (M : ℝ) / (84 * Real.log B) ≤ paperGeometricLogBudget d M B := by
  obtain ⟨M0, hM0⟩ := paperLogGrid_uniform_wide d B hd
  filter_upwards [eventually_ge_atTop M0] with M hM
  exact paperGeometricLogBudget_lower d M B hd hB fun m hm => hM0 M hM m (Finset.mem_Icc.mp hm).1

theorem tendsto_paperGeometricLogBudget (d B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    Tendsto (fun M => paperGeometricLogBudget d M B) atTop atTop := by
  have hh : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hlin : Tendsto (fun M : ℕ => (M : ℝ) / (84 * Real.log B)) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : 0 < (84 * Real.log B)⁻¹)
  exact tendsto_atTop_mono' atTop (paperGeometricLogBudget_eventually_lower d B hd hB) hlin

theorem paperGeometricIndices_eventually_nonempty (d B : ℕ) (hd : 1 ≤ d) (hB : 3 ≤ B) :
    ∀ᶠ M : ℕ in atTop, (paperGeometricIndices d M B).Nonempty := by
  filter_upwards [(tendsto_paperGeometricLogBudget d B hd hB).eventually_gt_atTop 0] with M hM
  by_contra he
  have hi := Finset.not_nonempty_iff_eq_empty.mp he
  simp only [paperGeometricLogBudget, hi, Finset.sum_empty] at hM
  exact (lt_irrefl 0) hM

/-- Once the actual grid is nonempty, any supplied nonempty prime batches
give an actual nonempty finite prime union. -/
theorem geometric_prime_union_nonempty (d M B : ℕ) (P : ℕ → Finset ℕ)
    (hI : (paperGeometricIndices d M B).Nonempty)
    (hP : ∀ j ∈ paperGeometricIndices d M B, 0 < (P j).card) :
    ((paperGeometricIndices d M B).biUnion P).Nonempty := by
  obtain ⟨j, hj⟩ := hI
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (hP j hj)
  exact ⟨p, Finset.mem_biUnion.mpr ⟨j, hj, hp⟩⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperScheduleX
#print axioms BinaryFormMoat.GeometryIntegration.paperLogGrid_uniform_wide
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricLogBudget_lower
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricLogBudget_eventually_lower
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_paperGeometricLogBudget
#print axioms BinaryFormMoat.GeometryIntegration.paperGeometricIndices_eventually_nonempty
#print axioms BinaryFormMoat.GeometryIntegration.geometric_prime_union_nonempty
