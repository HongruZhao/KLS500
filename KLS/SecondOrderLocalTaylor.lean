import KLS.QuadraticTestHessian
import Mathlib.Analysis.Calculus.MeanValue

/-! A genuine local second-order remainder estimate. Two mean-value estimates
bound a function with vanishing second jet by any positive multiple of the
squared distance in a sufficiently small neighborhood. -/

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma eventually_abs_le_sq_of_zero_second_jet {F : Space n → ℝ} {x₀ : Space n}
    (hF : ContDiffAt ℝ 2 F x₀) (hzero : F x₀ = 0)
    (hfirst : fderiv ℝ F x₀ = 0) (hsecond : fderiv ℝ (fderiv ℝ F) x₀ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x₀, |F y| ≤ ε * ‖y - x₀‖ ^ 2 := by
  have hc : ContinuousAt (fun z => ‖fderiv ℝ (fderiv ℝ F) z‖) x₀ :=
    ((hF.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)).norm
  have hn : ∀ᶠ z in 𝓝 x₀, ‖fderiv ℝ (fderiv ℝ F) z‖ < ε :=
    hc.eventually (Iio_mem_nhds (by
      change ‖fderiv ℝ (fderiv ℝ F) x₀‖ < ε
      rw [hsecond, ContinuousLinearMap.opNorm_zero]
      exact hε))
  have hd : ∀ᶠ z in 𝓝 x₀, ContDiffAt ℝ 2 F z := hF.eventually (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hd.and hn)
  filter_upwards [closedBall_mem_nhds x₀ hr] with y hy
  let ρ := ‖y - x₀‖
  have hρr : ρ ≤ r := hy
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hsub : closedBall x₀ ρ ⊆ closedBall x₀ r := closedBall_subset_closedBall hρr
  have hdfbound : ∀ z ∈ closedBall x₀ ρ, ‖fderiv ℝ F z‖ ≤ ε * ρ := by
    intro z hz
    have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ F) (s := closedBall x₀ ρ)
      (fun w hw => ((hball (hsub hw)).1.fderiv_right (m := 1)
        (by norm_num)).differentiableAt (by norm_num))
      (fun w hw => (hball (hsub hw)).2.le) (convex_closedBall x₀ ρ)
      (mem_closedBall_self hρ) hz
    rw [hfirst, sub_zero] at hmean
    exact hmean.trans (mul_le_mul_of_nonneg_left (show ‖z - x₀‖ ≤ ρ from hz) hε.le)
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le (f := F) (s := closedBall x₀ ρ)
    (fun z hz => (hball (hsub hz)).1.differentiableAt (by norm_num))
    hdfbound (convex_closedBall x₀ ρ) (mem_closedBall_self hρ)
    (show y ∈ closedBall x₀ ρ by
      simpa only [mem_closedBall, dist_eq_norm] using (le_rfl : ‖y - x₀‖ ≤ ‖y - x₀‖))
  rw [hzero, sub_zero, Real.norm_eq_abs] at hmean
  simpa only [ρ, pow_two, mul_assoc] using hmean

lemma secondFrechet_eq_of_coordinateHessian_eq {F G : Space n → ℝ} {x : Space n}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hG : DifferentiableAt ℝ (fderiv ℝ G) x)
    (heq : coordinateHessian F x = coordinateHessian G x) :
    fderiv ℝ (fderiv ℝ F) x = fderiv ℝ (fderiv ℝ G) x := by
  have hc (i j : Fin n) :
      fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fderiv ℝ G) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [← coordinateHessian_eq_fderiv_fderiv hF, ← coordinateHessian_eq_fderiv_fderiv hG, heq]
  ext v w
  rw [euclidean_eq_sum_single v, map_sum, map_sum]
  simp only [_root_.sum_apply, map_smul, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [euclidean_eq_sum_single w, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, hc]

/-- The actual quadratic Taylor polynomial, perturbed by a squared-distance
error, bounds the C2 function on a neighborhood. All hypotheses are local. -/
theorem eventually_abs_sub_centeredQuadratic_le_sq
    {F : Space n → ℝ} {x₀ : Space n} (hF : ContDiffAt ℝ 2 F x₀)
    (hpos : (coordinateHessian F x₀).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x₀,
      |F y - centeredQuadratic (coordinateHessian F x₀) x₀ (gradient F x₀) (F x₀) y| ≤
        ε * ‖y - x₀‖ ^ 2 := by
  let q := centeredQuadratic (coordinateHessian F x₀) x₀ (gradient F x₀) (F x₀)
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hqd : DifferentiableAt ℝ q x₀ := hq.differentiable (by norm_num) x₀
  have hFd : DifferentiableAt ℝ F x₀ := hF.differentiableAt (by norm_num)
  have hfirst : fderiv ℝ F x₀ = fderiv ℝ q x₀ := by
    ext v
    rw [← inner_gradient_left, ← inner_gradient_left, gradient_centeredQuadratic hpos]
    simp
  have hsecond : fderiv ℝ (fderiv ℝ F) x₀ = fderiv ℝ (fderiv ℝ q) x₀ := by
    apply secondFrechet_eq_of_coordinateHessian_eq
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀)
    exact (coordinateHessian_centeredQuadratic hpos _ _ _ _).symm
  have hfirstzero : fderiv ℝ (fun y => F y - q y) x₀ = 0 := by
    change fderiv ℝ (F - q) x₀ = 0
    rw [fderiv_sub hFd hqd, hfirst, sub_self]
  have hsecondzero : fderiv ℝ (fderiv ℝ (fun y => F y - q y)) x₀ = 0 := by
    have hevent : fderiv ℝ (fun y => F y - q y) =ᶠ[𝓝 x₀]
        (fun y => fderiv ℝ F y - fderiv ℝ q y) := by
      filter_upwards [hF.eventually (by norm_num)] with y hy
      exact fderiv_sub (hy.differentiableAt (by norm_num)) (hq.differentiable (by norm_num) y)
    rw [hevent.fderiv_eq]
    change fderiv ℝ (fderiv ℝ F - fderiv ℝ q) x₀ = 0
    rw [fderiv_sub
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀),
      hsecond, sub_self]
  exact eventually_abs_le_sq_of_zero_second_jet (hF.sub hq.contDiffAt)
    (by simp [q]) hfirstzero hsecondzero hε

end KLS
end

#print axioms KLS.eventually_abs_le_sq_of_zero_second_jet
#print axioms KLS.eventually_abs_sub_centeredQuadratic_le_sq
