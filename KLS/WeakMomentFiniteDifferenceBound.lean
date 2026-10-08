import KLS.WeakMomentFiniteDifferenceComparison
import KLS.WeakMomentDifferenceFirstOrder

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A uniformly convex target bounds actual finite differences of the original
weak moment potential. Source C2 regularity, a source Hessian, a global Hessian
bound, and smooth approximating transport laws are not hypotheses. -/
theorem weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (h x : Space n) : symmetricSecondDifference u h x ≤ 4 * ‖h‖ ^ 2 / κ := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush).differentiable
    (by norm_num)
  obtain ⟨xmin,hmin⟩ := exists_minimizer_of_finite_potentialMeasure hLip.continuous hc
  obtain ⟨C,hC,hbound⟩ := exists_bound_radial_target_derivative hV
    (bounded_gradient_of_weak_moment_transport hLip hc hV.continuous hK hKc hpush)
  have hreg (η : ℝ) (hη : 0 < η) :
      symmetricSecondDifference u h x ≤ 4 * ‖h‖ ^ 2 / κ +
        2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) + η * (u x - u xmin) := by
    obtain ⟨y,hy,hpde⟩ := exists_weak_moment_maximum_with_target_comparison
      hLip hc hV.continuous hK hKc hpush h hη
    let q := ‖(1/2 : ℝ) • (gradient u (y+h) - gradient u (y-h))‖
    have hdifference : symmetricSecondDifference u h y ≤ 2 * ‖h‖ * q := by
      have hh := (symmetricSecondDifference_le_gradient_difference hc hd h y).trans
        ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
      have heq : q = (1/2 : ℝ) * ‖gradient u (y+h) - gradient u (y-h)‖ := by
        dsimp [q]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      rw [heq]
      nlinarith
    have hquad : κ * q ^ 2 ≤ 2 * ‖h‖ * q + η * ((n : ℝ) + C) := by
      have hlo := target_gap_lower_at_penalized_max hd (hV.differentiable (by norm_num))
        hVc hstrong h η y hy
      have hb := (neg_abs_le (fderiv ℝ V (gradient u y) (gradient u y))).trans'
        (neg_le_neg (hbound y))
      have hb' := mul_le_mul_of_nonneg_left hb hη.le
      dsimp [q] at *
      nlinarith
    have hqbound : q ≤ 2 * ‖h‖ / κ + Real.sqrt (η * ((n : ℝ) + C) / κ) :=
      le_linear_add_sqrt_of_quadratic hκ (norm_nonneg h) (by positivity) (norm_nonneg _) hquad
    have hdy : symmetricSecondDifference u h y ≤ 4 * ‖h‖ ^ 2 / κ +
        2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) := by
      have hh := hdifference.trans (mul_le_mul_of_nonneg_left hqbound (by positivity : 0 ≤ 2 * ‖h‖))
      convert hh using 1
      ring
    have hxy := hy x
    have hmy := mul_le_mul_of_nonneg_left (hmin y) hη.le
    linarith
  have heta := cutoffScale_tendsto_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((heta.mul_const ((n : ℝ) + C)).div_const κ)
  have hlim := (((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => 4 * ‖h‖ ^ 2 / κ) atTop (𝓝 (4 * ‖h‖ ^ 2 / κ))).add
      (hs.const_mul (2 * ‖h‖))).add
    (heta.mul_const (u x - u xmin)))
  have hlim' : Tendsto (fun k => 4 * ‖h‖ ^ 2 / κ +
      2 * ‖h‖ * Real.sqrt (cutoffScale k * ((n : ℝ) + C) / κ) +
      cutoffScale k * (u x - u xmin)) atTop (𝓝 (4 * ‖h‖ ^ 2 / κ)) := by
    simpa only [zero_mul, zero_div, Real.sqrt_zero, mul_zero, add_zero, Function.comp_def] using hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall fun k => hreg _ (cutoffScale_pos k))


end KLS
end
