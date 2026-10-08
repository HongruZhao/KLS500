import KLS.ThirdCumulant

/-!+# Full affine dimension from isotropy

An isotropic probability cannot be concentrated on a proper affine hyperplane.
This discharges the support nondegeneracy needed by moment-measure arguments.
It does not assert absolute continuity, which requires additional log-concavity.
-/

open MeasureTheory ProbabilityTheory Set Filter

noncomputable section
namespace KLS

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem IsIsotropic.eq_zero_of_ae_inner_eq_const
    (hμ : IsIsotropic μ) {u : Space n} {c : ℝ}
    (h : (fun x : Space n => inner ℝ x u) =ᵐ[μ] fun _ => c) : u = 0 := by
  have hv : ‖u‖ ^ 2 = 0 := by
    rw [← hμ.real_variance_inner u, ProbabilityTheory.variance_congr h]
    simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hv)

theorem IsIsotropic.measure_hyperplane_lt_one
    (hμ : IsIsotropic μ) {u : Space n} (hu : u ≠ 0) (c : ℝ) :
    μ {x : Space n | inner ℝ x u = c} < 1 := by
  apply lt_of_le_of_ne prob_le_one
  intro heq
  have hm : MeasurableSet {x : Space n | inner ℝ x u = c} := by
    exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet
  have hae : (fun x : Space n => inner ℝ x u) =ᵐ[μ] fun _ => c :=
    (mem_ae_iff_prob_eq_one hm).2 heq
  exact hu (hμ.eq_zero_of_ae_inner_eq_const hae)

theorem IsIsotropic.support_not_subset_hyperplane
    (hμ : IsIsotropic μ) {u : Space n} (hu : u ≠ 0) (c : ℝ) :
    ¬ μ.support ⊆ {x : Space n | inner ℝ x u = c} := by
  intro hsub
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  have hae : (fun x : Space n => inner ℝ x u) =ᵐ[μ] fun _ => c :=
    hsupp.mono hsub
  exact hu (hμ.eq_zero_of_ae_inner_eq_const hae)

/-- No proper affine subspace has full mass. This includes translated
subspaces, not only linear subspaces through the mean. -/
theorem IsIsotropic.affineSubspace_eq_top_of_ae_mem
    (hμ : IsIsotropic μ) (s : AffineSubspace ℝ (Space n))
    (hs : ∀ᵐ x ∂μ, x ∈ s) : s = ⊤ := by
  obtain ⟨p, hp⟩ := hs.exists
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p, hp⟩).mp
  apply (Submodule.orthogonal_eq_bot_iff).mp
  apply eq_bot_iff.mpr
  intro u hu
  change u = 0
  apply hμ.eq_zero_of_ae_inner_eq_const (c := inner ℝ p u)
  filter_upwards [hs] with x hx
  have hzero : inner ℝ (x - p) u = 0 :=
    (s.direction.mem_orthogonal u).1 hu (x - p)
      (AffineSubspace.vsub_mem_direction hx hp)
  rw [inner_sub_left] at hzero
  exact sub_eq_zero.mp hzero

/-- The topological support of an isotropic probability spans the entire
ambient affine space. No log-concavity is needed for this conclusion. -/
theorem IsIsotropic.affineSpan_support_eq_top
    (hμ : IsIsotropic μ) : affineSpan ℝ μ.support = ⊤ := by
  apply hμ.affineSubspace_eq_top_of_ae_mem
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  exact hsupp.mono (fun x hx => subset_affineSpan ℝ μ.support hx)

end KLS
end

#print axioms KLS.IsIsotropic.eq_zero_of_ae_inner_eq_const
#print axioms KLS.IsIsotropic.measure_hyperplane_lt_one
#print axioms KLS.IsIsotropic.support_not_subset_hyperplane
#print axioms KLS.IsIsotropic.affineSubspace_eq_top_of_ae_mem
#print axioms KLS.IsIsotropic.affineSpan_support_eq_top
