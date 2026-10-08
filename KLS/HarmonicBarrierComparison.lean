import KLS.IdentityHessianPerturbation

/-! An actual O(epsilon²) nonlinear comparison estimate for a weak
Monge--Ampere solution and a smooth harmonic correction of a quadratic.
The smooth comparator is supplied explicitly. No Hessian or classical
regularity of the weak solution is assumed or concluded. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A dimension-dependent constant from the exact determinant polynomial. -/
def nonlinearComparisonConstant (n : ℕ) : ℝ :=
  Classical.choose (exists_uniform_det_identity_quadratic_bound n) + 2

lemma nonlinearComparisonConstant_gt_two (n : ℕ) :
    2 < nonlinearComparisonConstant n := by
  have h := (Classical.choose_spec (exists_uniform_det_identity_quadratic_bound n)).1
  dsimp [nonlinearComparisonConstant]
  linarith

lemma coordinateHessian_quadratic_add_harmonic {h : Space n → ℝ}
    (hh : ContDiff ℝ 2 h) (x₀ p : Space n) (c ε : ℝ) (x : Space n) :
    coordinateHessian (fun y =>
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c y + ε * h y) x =
      1 + ε • coordinateHessian h x := by
  have hq : ContDiff ℝ 2 (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c) :=
    (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  ext i j
  have hadd := coordinateHessian_add hq (hh.const_smul ε) x i j
  have hscale := coordinateHessian_smul hh ε x i j
  have hqH := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
    (coordinateHessian_centeredQuadratic Matrix.PosSemidef.one x₀ p c x)
  exact hadd.trans (congrArg₂ (fun a b : ℝ => a + b) hqH hscale)

/-- A quantitative comparison theorem for the actual weak equation. The
harmonicity and Hessian bound concern only the given smooth correction h. -/
theorem abs_sub_quadratic_harmonic_le
    (hn : 0 < n) {u f h : Space n → ℝ}
    (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hh : ContDiff ℝ 2 h) (x₀ p : Space n) (c R η ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / (2 * nonlinearComparisonConstant n))
    (hboundary : ∀ x ∈ frontier (closedBall x₀ R),
      |u x - (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x + ε * h x)| ≤ η)
    (hharmonic : ∀ x ∈ interior (closedBall x₀ R), coordinateLaplacian h x = 0)
    (hhessian : ∀ x ∈ interior (closedBall x₀ R), ‖matrixAction (coordinateHessian h x)‖ ≤ 1 / 2)
    (hdensity : ∀ x ∈ interior (closedBall x₀ R), |f x - 1| ≤ ε ^ 2) :
    ∀ x ∈ closedBall x₀ R,
      |u x - (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x + ε * h x)| ≤
        η + nonlinearComparisonConstant n * ε ^ 2 / 2 * (R ^ 2 - ‖x - x₀‖ ^ 2) := by
  let C := Classical.choose (exists_uniform_det_identity_quadratic_bound n)
  have hC := Classical.choose_spec (exists_uniform_det_identity_quadratic_bound n)
  have hD : nonlinearComparisonConstant n = C + 2 := rfl
  have hεsmall' : ε ≤ 1 / (2 * (C + 2)) := by simpa only [hD] using hεsmall
  have hε1 : |ε| ≤ 1 := by
    rw [abs_of_pos hε]
    have hd : 0 < 2 * (C + 2) := by dsimp [C]; linarith [hC.1]
    have he := (le_div_iff₀ hd).mp hεsmall'
    have hcp : 0 < C := hC.1
    nlinarith
  let v : Space n → ℝ := fun x =>
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x + ε * h x
  have hv : ContDiff ℝ 2 v :=
    ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)).add (contDiff_const.mul hh)
  have hHv (x : Space n) : coordinateHessian v x = 1 + ε • coordinateHessian h x :=
    coordinateHessian_quadratic_add_harmonic hh x₀ p c ε x
  apply abs_sub_smooth_le_of_det_gaps_on_closedBall hu huc hf hf0 hMA hv
    x₀ R η (nonlinearComparisonConstant n * ε ^ 2) hboundary
  · intro x hx
    rw [hHv]
    apply Matrix.PosSemidef.add
      (posDef_one_add_smul_of_matrixAction_norm_le_half
        (coordinateHessian_symmetric hh x) (hhessian x hx) hε1).posSemidef
    exact Matrix.PosSemidef.one.smul (by positivity [nonlinearComparisonConstant_gt_two n])
  · intro x hx
    rw [hHv, hD]
    exact (determinant_gaps_of_trace_zero_perturbation hn hC.1 hC.2
      ((elementwise_matrix_norm_le_matrixAction_norm _).trans (hhessian x hx))
      (hharmonic x hx) hε hεsmall' (hdensity x hx)).1
  · intro x hx
    rw [hHv, hD]
    exact (determinant_gaps_of_trace_zero_perturbation hn hC.1 hC.2
      ((elementwise_matrix_norm_le_matrixAction_norm _).trans (hhessian x hx))
      (hharmonic x hx) hε hεsmall' (hdensity x hx)).2

/-- The same quantitative comparison for the original finite-mass weak moment
transport, consuming its actual exponential Alexandrov density. -/
theorem moment_abs_sub_quadratic_harmonic_le
    (hn : 0 < n) {u V h : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hh : ContDiff ℝ 2 h) (x₀ p : Space n) (c R η ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / (2 * nonlinearComparisonConstant n))
    (hboundary : ∀ x ∈ frontier (closedBall x₀ R),
      |u x - (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x + ε * h x)| ≤ η)
    (hharmonic : ∀ x ∈ interior (closedBall x₀ R), coordinateLaplacian h x = 0)
    (hhessian : ∀ x ∈ interior (closedBall x₀ R), ‖matrixAction (coordinateHessian h x)‖ ≤ 1 / 2)
    (hdensity : ∀ x ∈ interior (closedBall x₀ R), |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2) :
    ∀ x ∈ closedBall x₀ R,
      |u x - (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x + ε * h x)| ≤
        η + nonlinearComparisonConstant n * ε ^ 2 / 2 * (R ^ 2 - ‖x - x₀‖ ^ 2) := by
  exact abs_sub_quadratic_harmonic_le hn hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush)
    (fun x => Real.exp_nonneg _) (fun S hS =>
      subgradient_volume_eq_lintegral_real_moment_density hLip hc hV.measurable
        hK.measurableSet hKc hpush hS)
    hh x₀ p c R η ε hε hεsmall hboundary hharmonic hhessian hdensity

end KLS
end
