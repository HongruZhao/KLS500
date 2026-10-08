import KLS.AdaptiveDeterminantNoncollapse
import KLS.LocalizationLipschitz

/-! Compact-support bounds on covariance and compactness bounds on its inverse. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem norm_mean_le_of_support (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (p : Parameter n) : ‖mean μ p.1 p.2‖ ≤ R := by
  letI := law_isProbability hμ p.1 p.2
  letI : IsProbabilityMeasure (μ.tilted (exponent p.1 p.2)) := law_isProbability hμ p.1 p.2
  apply (pi_norm_le_iff_of_nonneg hR0).mpr
  intro i
  have hb : ∀ᵐ x ∂law μ p.1 p.2, ‖x i‖ ≤ R :=
    (ae_norm_le_law hμ hR p).mono fun x hx => (PiLp.norm_apply_le x i).trans hx
  simpa [mean] using norm_integral_le_of_norm_le_const hb

theorem norm_covariance_le_of_support (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (p : Parameter n) : ‖covariance μ p.1 p.2‖ ≤ 2*R^2 := by
  letI := law_isProbability hμ p.1 p.2
  letI : IsProbabilityMeasure (μ.tilted (exponent p.1 p.2)) := law_isProbability hμ p.1 p.2
  have hB : 0 ≤ 2*R^2 := by positivity
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  have hb (a : Fin n) : ∀ᵐ x ∂law μ p.1 p.2, ‖x a‖ ≤ R :=
    (ae_norm_le_law hμ hR p).mono fun x hx => (PiLp.norm_apply_le x a).trans hx
  have hh := KLS.StandardLocalization.norm_covariance_le_of_bounds
    (memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop)) hR0 hR0 (hb i) (hb j)
  calc _ ≤ 2*R*R := hh
    _ = _ := by ring

/-- Inversion is uniformly bounded on the compact set with bounded norm and
strictly positive determinant. No spectral decomposition or process limit is assumed. -/
theorem exists_matrix_inverse_bound (M δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
      ‖A‖ ≤ M → δ ≤ A.det → ‖A⁻¹‖ ≤ C := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) := Metric.closedBall 0 M ∩ {A | δ ≤ A.det}
  have hK : IsCompact K := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) M).inter_right
    (isClosed_le continuous_const continuous_id.matrix_det)
  have hi : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) K := by
    intro A hA
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_matrix_inv
    simpa only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using
      continuousAt_inv₀ (hδ.trans_le hA.2).ne'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨max C 0, le_max_right _ _, fun A hA hdet => ?_⟩
  apply (hC A ?_).trans (le_max_left _ _)
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hA, hdet⟩

theorem norm_inverseSqrtCovariance_le_of_inverse (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ‖inverseCovariance μ p‖ ≤ C) :
    ‖inverseSqrtCovariance μ p‖ ≤ C+1 := by
  have hB : 0 ≤ C+1 := by linarith
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  have hs : (∑ k : Fin n, inverseSqrtCovariance μ p i k * inverseSqrtCovariance μ p i k) =
      inverseCovariance μ p i i := by
    have he := congrFun (congrFun (inverseSqrtCovariance_mul_transpose hμ hfull p) i) i
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using he
  have hsq : inverseSqrtCovariance μ p i j * inverseSqrtCovariance μ p i j ≤
      inverseCovariance μ p i i := by
    rw [← hs]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
  have hii : |inverseCovariance μ p i i| ≤ C :=
    ((norm_le_pi_norm (inverseCovariance μ p i) i).trans
      (norm_le_pi_norm (inverseCovariance μ p) i)).trans hC
  rw [Real.norm_eq_abs]
  nlinarith [le_abs_self (inverseCovariance μ p i i),
    sq_abs (inverseSqrtCovariance μ p i j), sq_nonneg (|inverseSqrtCovariance μ p i j| - 1/2)]

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.exists_matrix_inverse_bound
#print axioms KLS.AdaptiveLocalization.norm_inverseSqrtCovariance_le_of_inverse
