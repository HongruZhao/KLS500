import KLS.TruncatedConjugate

/-! Centering a ball-truncated conjugate at a point strictly inside the source
ball gives a continuous convex globally coercive potential with finite
exponential mass. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem exists_linear_lower_bound_truncatedLegendrePotential
    {u : Space n → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℝ, ∀ p, M * ‖p‖ - B ≤ truncatedLegendrePotential u M p := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space n) M).bddAbove_image hu.continuousOn
  refine ⟨B, ?_⟩
  intro p
  by_cases hp : p = 0
  · have h0 : u 0 ≤ B := hB ⟨0, mem_closedBall_self hM, rfl⟩
    have hh := le_truncatedLegendrePotential hu M p (norm_zero.trans_le hM)
    simp only [hp, norm_zero, inner_zero_right, mul_zero, zero_sub] at hh ⊢
    linarith
  · have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let y : Space n := (M / ‖p‖) • p
    have hyn : ‖y‖ = M := by
      simp only [y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hM hpn.le), div_mul_cancel₀ _ hpn.ne']
    have hyball : y ∈ closedBall (0 : Space n) M := by
      simpa only [mem_closedBall, dist_zero_right, hyn] using (le_rfl : M ≤ M)
    have hyB : u y ≤ B := hB ⟨y, hyball, rfl⟩
    have hh := le_truncatedLegendrePotential hu M p hyn.le
    have hip : inner ℝ p y = M * ‖p‖ := by
      simp only [y, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hip] at hh
    linarith

theorem continuous_centeredTruncatedConjugate
    {u : Space n → ℝ} (hu : Continuous u) (x : Space n) {M : ℝ} (hM : 0 ≤ M) :
    Continuous (centeredTruncatedConjugate u x M) := by
  exact ((lipschitzWith_truncatedLegendrePotential hu hM).continuous.sub
    (continuous_const.inner continuous_id)).add continuous_const

theorem convexOn_centeredTruncatedConjugate
    {u : Space n → ℝ} (hu : Continuous u) (x : Space n) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (centeredTruncatedConjugate u x M) := by
  exact (convexOn_tiltedPotential (convexOn_truncatedLegendrePotential hu hM) x).add_const (u x)

theorem exists_linear_lower_bound_centeredTruncatedConjugate
    {u : Space n → ℝ} (hu : Continuous u) {x : Space n} {M : ℝ} (hx : ‖x‖ < M) :
    ∃ a A : ℝ, 0 < a ∧ ∀ p, a * ‖p‖ - A ≤ centeredTruncatedConjugate u x M p := by
  obtain ⟨B, hB⟩ := exists_linear_lower_bound_truncatedLegendrePotential hu
    (norm_nonneg x |>.trans hx.le)
  refine ⟨M - ‖x‖, B - u x, sub_pos.mpr hx, ?_⟩
  intro p
  have hh := hB p
  have hi := real_inner_le_norm x p
  dsimp [centeredTruncatedConjugate]
  nlinarith

theorem isFiniteMeasure_potentialMeasure_centeredTruncatedConjugate
    {u : Space n → ℝ} (hu : Continuous u) {x : Space n} {M : ℝ} (hx : ‖x‖ < M) :
    IsFiniteMeasure (potentialMeasure (centeredTruncatedConjugate u x M)) := by
  obtain ⟨a, A, ha, hbound⟩ := exists_linear_lower_bound_centeredTruncatedConjugate hu hx
  have hint := integrable_exp_neg_of_linear_coercivity
    (continuous_centeredTruncatedConjugate hu x (norm_nonneg x |>.trans hx.le)).aestronglyMeasurable
    ha hbound
  exact isFiniteMeasure_withDensity_ofReal hint.2

end KLS
end

#print axioms KLS.exists_linear_lower_bound_truncatedLegendrePotential
#print axioms KLS.exists_linear_lower_bound_centeredTruncatedConjugate
#print axioms KLS.isFiniteMeasure_potentialMeasure_centeredTruncatedConjugate
