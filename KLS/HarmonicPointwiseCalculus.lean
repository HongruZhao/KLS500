import KLS.ViscosityHarmonicRegularity
import KLS.HessianMetricProduct
import KLS.MomentMapFiniteDifference

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Sum of the squares of the actual coordinate derivatives. -/
def harmonicGradientSquare (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, coordinateDerivative f i x ^ 2

lemma harmonicGradientSquare_nonneg (f : Space n → ℝ) (x : Space n) :
    0 ≤ harmonicGradientSquare f x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma coordinateDerivative_sq_le_harmonicGradientSquare (f : Space n → ℝ)
    (x : Space n) (i : Fin n) :
    coordinateDerivative f i x ^ 2 ≤ harmonicGradientSquare f x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (coordinateDerivative f j x)) (Finset.mem_univ i)

lemma harmonicGradientSquare_eq_norm_gradient_sq (f : Space n → ℝ) (x : Space n) :
    harmonicGradientSquare f x = ‖gradient f x‖ ^ 2 := by
  simp only [harmonicGradientSquare, pow_two, sum_coordinateDerivative_mul,
    real_inner_self_eq_norm_sq]

lemma coordinateLaplacian_smul {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (a : ℝ) (x : Space n) :
    coordinateLaplacian (a • f) x = a * coordinateLaplacian f x := by
  simp only [coordinateLaplacian, coordinateHessian_smul hf, Finset.mul_sum]

lemma coordinateLaplacian_mul {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    coordinateLaplacian (fun y => f y * g y) x =
      coordinateLaplacian f x * g x + 2 * (∑ i, coordinateDerivative f i x * coordinateDerivative g i x) +
        f x * coordinateLaplacian g x := by
  simp only [coordinateLaplacian, coordinateHessian_mul hf hg,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma coordinateLaplacian_sq {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (x : Space n) :
    coordinateLaplacian (fun y => f y ^ 2) x =
      2 * f x * coordinateLaplacian f x + 2 * harmonicGradientSquare f x := by
  simp_rw [pow_two]
  rw [coordinateLaplacian_mul hf hf]
  simp only [harmonicGradientSquare, pow_two]
  ring

lemma coordinateLaplacian_coordinateDerivative {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin n) (x : Space n) :
    coordinateLaplacian (coordinateDerivative f i) x = coordinateDerivative (coordinateLaplacian f) i x := by
  unfold coordinateLaplacian
  rw [coordinateDerivative_sum (fun j =>
    (contDiff_coordinateHessian hf (m := 1) (by norm_num) j j).differentiable (by norm_num) x)]
  exact Finset.sum_congr rfl (fun j _ => (coordinateDerivative_diagonal_eq hf i j x).symm)

lemma coordinateLaplacian_nonpos_of_isLocalMax {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) {x : Space n} (hm : IsLocalMax F x) :
    coordinateLaplacian F x ≤ 0 := by
  have hdir (v : Space n) : fderiv ℝ (fderiv ℝ F) x v v ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    have hs : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x - t • v) := by fun_prop
      simpa only [zero_smul, sub_zero] using hc.tendsto (0 : ℝ)
    apply le_of_tendsto (tendsto_symmetricSecondDifference_directional hF x v)
    have hmax : ∀ᶠ y in 𝓝 x, F y ≤ F x := hm
    filter_upwards [(ht.eventually hmax).filter_mono nhdsWithin_le_nhds,
      (hs.eventually hmax).filter_mono nhdsWithin_le_nhds] with t hp hn
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
    unfold symmetricSecondDifference
    linarith
  unfold coordinateLaplacian
  apply Finset.sum_nonpos
  intro i _
  rw [coordinateHessian_eq_fderiv_fderiv
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
  exact hdir _

lemma coordinateLaplacian_derivative_eq_zero_on {f : Space n → ℝ}
    (hf : ContDiff ℝ 3 f) {U : Set (Space n)} (hU : IsOpen U)
    (hharm : ∀ x ∈ U, coordinateLaplacian f x = 0) (i : Fin n) {x : Space n} (hx : x ∈ U) :
    coordinateLaplacian (coordinateDerivative f i) x = 0 := by
  rw [coordinateLaplacian_coordinateDerivative hf]
  have he : coordinateLaplacian f =ᶠ[𝓝 x] (0 : Space n → ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hharm y hy
  unfold coordinateDerivative
  rw [he.fderiv_eq]
  simp

end KLS
end
