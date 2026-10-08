import KLS.C2BarrierComparison
import KLS.MomentQuadraticBarrier

/-! Quantitative comparison with an arbitrary smooth approximate solution.
Strict determinant gaps for its actual Hessian plus/minus a scalar identity
control the value error of the weak solution on a ball. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS

variable {n : ℕ}

lemma centeredQuadratic_one_eq_half_norm_sq (x₀ x : Space n) :
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 x = ‖x - x₀‖ ^ 2 / 2 := by
  simp only [centeredQuadratic, inner_zero_left, zero_add, matrixAction_one_apply,
    real_inner_self_eq_norm_sq]
  ring

lemma coordinateHessian_add_scalar_quadratic_const {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (x₀ : Space n) (a c : ℝ) (x : Space n) :
    coordinateHessian (fun y => v y + a *
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 y + c) x =
      coordinateHessian v x + a • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [coordinateHessian_add_const]
  have hq : ContDiff ℝ 2 (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0) :=
    (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  ext i j
  change coordinateHessian (v + a • centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0) x i j = _
  have hadd := coordinateHessian_add hv (hq.const_smul a) x i j
  have hscale := coordinateHessian_smul hq a x i j
  have hqH := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
    (coordinateHessian_centeredQuadratic Matrix.PosSemidef.one x₀ 0 0 x)
  exact hadd.trans (congrArg (fun z => coordinateHessian v x i j + z)
    (hscale.trans (congrArg (fun z => a * z) hqH)))

/-- Actual nonlinear comparison with a smooth comparator. The only Hessians in
its hypotheses are those of v, never those of the weak solution u. -/
theorem abs_sub_smooth_le_of_det_gaps_on_closedBall
    {u f v : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hv : ContDiff ℝ 2 v) (x₀ : Space n) (R η τ : ℝ)
    (hboundary : ∀ x ∈ frontier (closedBall x₀ R), |u x - v x| ≤ η)
    (hplus : ∀ x ∈ interior (closedBall x₀ R),
      (coordinateHessian v x + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hdetminus : ∀ x ∈ interior (closedBall x₀ R),
      (coordinateHessian v x - τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det < f x)
    (hdetplus : ∀ x ∈ interior (closedBall x₀ R),
      f x < (coordinateHessian v x + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :
    ∀ x ∈ closedBall x₀ R,
      |u x - v x| ≤ η + τ / 2 * (R ^ 2 - ‖x - x₀‖ ^ 2) := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  let ψhi : Space n → ℝ := fun x => v x + (-τ) * q x + (η + τ * R ^ 2 / 2)
  let ψlo : Space n → ℝ := fun x => v x + τ * q x + (-η - τ * R ^ 2 / 2)
  have hhi : ContDiff ℝ 2 ψhi := (hv.add (contDiff_const.mul hq)).add contDiff_const
  have hlo : ContDiff ℝ 2 ψlo := (hv.add (contDiff_const.mul hq)).add contDiff_const
  have hHhi (x : Space n) : coordinateHessian ψhi x =
      coordinateHessian v x - τ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [ψhi, q, neg_smul, sub_eq_add_neg] using
      coordinateHessian_add_scalar_quadratic_const hv x₀ (-τ) (η + τ * R ^ 2 / 2) x
  have hHlo (x : Space n) : coordinateHessian ψlo x =
      coordinateHessian v x + τ • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    coordinateHessian_add_scalar_quadratic_const hv x₀ τ (-η - τ * R ^ 2 / 2) x
  have hqb (x : Space n) (hx : x ∈ frontier (closedBall x₀ R)) : q x = R ^ 2 / 2 := by
    have hd : ‖x - x₀‖ = R := frontier_closedBall_subset_sphere hx
    rw [show q x = ‖x - x₀‖ ^ 2 / 2 from centeredQuadratic_one_eq_half_norm_sq x₀ x, hd]
  have huhi : ∀ x ∈ closedBall x₀ R, u x ≤ ψhi x := by
    apply le_of_strict_c2_upper_barrier hu huc hf hMA (isCompact_closedBall x₀ R) hhi
    · intro x hx
      have hb := (abs_le.mp (hboundary x hx)).2
      dsimp [ψhi]
      rw [hqb x hx]
      linarith
    · intro x hx
      rw [hHhi]
      exact hdetminus x hx
  have hlou : ∀ x ∈ closedBall x₀ R, ψlo x ≤ u x := by
    apply le_of_strict_c2_lower_barrier hu huc hf hf0 hMA (isCompact_closedBall x₀ R) hlo
    · intro x hx
      have hb := (abs_le.mp (hboundary x hx)).1
      dsimp [ψlo]
      rw [hqb x hx]
      linarith
    · intro x hx
      rw [hHlo]
      exact hplus x hx
    · intro x hx
      rw [hHlo]
      exact hdetplus x hx
  intro x hx
  have hh := huhi x hx
  have hl := hlou x hx
  dsimp [ψhi, ψlo] at hh hl
  rw [show q x = ‖x - x₀‖ ^ 2 / 2 from centeredQuadratic_one_eq_half_norm_sq x₀ x] at hh hl
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The comparison estimate for the original weak moment transport, with its
actual exponential Alexandrov density. -/
theorem moment_abs_sub_smooth_le_of_det_gaps_on_closedBall
    {u V v : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hv : ContDiff ℝ 2 v) (x₀ : Space n) (R η τ : ℝ)
    (hboundary : ∀ x ∈ frontier (closedBall x₀ R), |u x - v x| ≤ η)
    (hplus : ∀ x ∈ interior (closedBall x₀ R),
      (coordinateHessian v x + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hdetminus : ∀ x ∈ interior (closedBall x₀ R),
      (coordinateHessian v x - τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det <
        Real.exp (-u x + V (gradient u x)))
    (hdetplus : ∀ x ∈ interior (closedBall x₀ R),
      Real.exp (-u x + V (gradient u x)) <
        (coordinateHessian v x + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :
    ∀ x ∈ closedBall x₀ R,
      |u x - v x| ≤ η + τ / 2 * (R ^ 2 - ‖x - x₀‖ ^ 2) := by
  exact abs_sub_smooth_le_of_det_gaps_on_closedBall hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush)
    (fun x => Real.exp_nonneg _) (fun S hS =>
      subgradient_volume_eq_lintegral_real_moment_density hLip hc hV.measurable
        hK.measurableSet hKc hpush hS)
    hv x₀ R η τ hboundary hplus hdetminus hdetplus

end KLS
end
