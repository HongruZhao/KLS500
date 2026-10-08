import KLS.WeightedMollification
import KLS.ConvexHessian

open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped Topology ContDiff NNReal Convolution
noncomputable section
namespace KLS
variable {n : ℕ}

lemma mollify_eq_integral_kernel_left (k : ℕ) (u : Space n → ℝ) (x : Space n) :
    mollify k u x = ∫ y, mollifierKernel n k y * u (x - y) := by
  have he : scalarConvolution u (mollifierKernel n k) =
      scalarConvolution (mollifierKernel n k) u :=
    convolution_symm (lsmul ℝ ℝ) (by ext; simp)
  exact congrFun he x

lemma integrable_mollifier_left {u : Space n → ℝ} (hu : Continuous u)
    (k : ℕ) (x : Space n) :
    Integrable (fun y => mollifierKernel n k y * u (x - y)) := by
  exact (mollifierKernel_hasCompactSupport k).convolutionExists_left (lsmul ℝ ℝ)
    (mollifierKernel_contDiff k).continuous hu.locallyIntegrable x

lemma mollify_add_const {u : Space n → ℝ} (hu : Continuous u) (k : ℕ) (c : ℝ) :
    mollify k (fun x => u x + c) = fun x => mollify k u x + c := by
  funext x
  rw [mollify_eq_integral_kernel_left, mollify_eq_integral_kernel_left]
  simp_rw [mul_add]
  have hi : Integrable (fun y => mollifierKernel n k y * c) :=
    (mollifierBump n k).integrable_normed.mul_const c
  rw [integral_add (integrable_mollifier_left hu k x) hi, integral_mul_const]
  simp only [mollifierKernel, (mollifierBump n k).integral_normed, one_mul]

/-- Convolution with the actual nonnegative normalized bump preserves convexity. -/
theorem convexOn_mollify {u : Space n → ℝ} (hu : Continuous u)
    (hc : ConvexOn ℝ univ u) (k : ℕ) : ConvexOn ℝ univ (mollify k u) := by
  refine ⟨convex_univ,?_⟩
  intro x _ z _ a b ha hb hab
  simp only [mollify_eq_integral_kernel_left, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_mollifier_left hu k x).const_mul a)
    ((integrable_mollifier_left hu k z).const_mul b)]
  apply integral_mono (integrable_mollifier_left hu k (a • x + b • z))
    (((integrable_mollifier_left hu k x).const_mul a).add
      ((integrable_mollifier_left hu k z).const_mul b))
  intro y
  have hh := hc.2 (mem_univ (x-y)) (mem_univ (z-y)) ha hb hab
  have he : a • (x-y) + b • (z-y) = a • x + b • z - y := by
    rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul]
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh ((mollifierBump n k).nonneg_normed (μ := volume) y)
  change mollifierKernel n k y * u (a • x + b • z - y) ≤
    a * (mollifierKernel n k y * u (x-y)) + b * (mollifierKernel n k y * u (z-y))
  calc
    _ ≤ mollifierKernel n k y * (a * u (x-y) + b * u (z-y)) := hm
    _ = _ := by ring

/-- A global Lipschitz input has a uniform error bounded by the actual bump radius. -/
theorem dist_mollify_le_of_lipschitz {u : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L u) (k : ℕ) (x : Space n) :
    dist (mollify k u x) (u x) ≤ L * (2 * cutoffScale k) := by
  have hh := (mollifierBump n k).dist_normed_convolution_le
    (μ := (volume : Measure (Space n))) hLip.continuous.aestronglyMeasurable
    (fun y (hy : y ∈ ball x (mollifierBump n k).rOut) =>
      (hLip.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg))
  simpa only [mollify_eq_integral_kernel_left, mollifierBump, mollifierKernel,
    scalarConvolution, convolution, lsmul_apply, smul_eq_mul] using hh

/-- Continuous inputs converge under actual mollification also at moving points. -/
theorem mollify_tendsto_at_moving_points {u : Space n → ℝ} (hu : Continuous u)
    {x : ℕ → Space n} {x₀ : Space n} (hx : Tendsto x atTop (𝓝 x₀))
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => mollify (s k) u (x k)) atTop (𝓝 (u x₀)) := by
  have hr : Tendsto (fun k => (mollifierBump n (s k)).rOut) atTop (𝓝 0) := by
    simpa only [mollifierBump, mul_zero, Function.comp_def] using (cutoffScale_tendsto_zero.comp hs).const_mul 2
  have ht := ContDiffBump.convolution_tendsto_right hr
    (μ := (volume : Measure (Space n)))
    (Eventually.of_forall fun _ => hu.aestronglyMeasurable)
    ((hu.tendsto x₀).comp tendsto_snd) hx
  simpa only [mollify_eq_integral_kernel_left, mollifierKernel,
    convolution, lsmul_apply, smul_eq_mul] using ht

end KLS
end
