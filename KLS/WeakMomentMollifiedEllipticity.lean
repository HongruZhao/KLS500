import KLS.MollifiedFiniteDifferenceHessian
import KLS.MatrixDeterminantCompactEllipticity

open MeasureTheory Set Filter Matrix Metric InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise Pointwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A lower bound on the actual radius-two input enlargement bounds every
member of the fixed mollifier sequence on the original compact set. -/
theorem lower_le_mollify_on_enlargement
    {f : Space n → ℝ} (hf : Continuous f) {S : Set (Space n)} {B : ℝ}
    (hB : ∀ y ∈ mollifierEnlargement S, B ≤ f y) (k : ℕ) {x : Space n} (hx : x ∈ S) :
    B ≤ mollify k f x := by
  rw [mollify_eq_integral_kernel_left]
  have hi : Integrable (fun y => mollifierKernel n k y * B) :=
    (mollifierBump n k).integrable_normed.mul_const B
  calc
    B = ∫ y, mollifierKernel n k y * B := by
      rw [integral_mul_const]
      simp only [mollifierKernel,(mollifierBump n k).integral_normed,one_mul]
    _ ≤ _ := by
      apply integral_mono hi (integrable_mollifier_left hf k x)
      intro y
      by_cases hy : mollifierKernel n k y = 0
      · simp only [hy,zero_mul,le_refl]
      · have hys := mollifierKernel_support_subset k (Function.mem_support.mpr hy)
        have hyn : -y ∈ closedBall (0 : Space n) 2 := by simpa using hys
        have hxy : x-y ∈ mollifierEnlargement S := by
          simpa only [mollifierEnlargement,sub_eq_add_neg] using Set.add_mem_add hx hyn
        exact mul_le_mul_of_nonneg_left (hB _ hxy) ((mollifierBump n k).nonneg_normed y)

/-- Every actual mollification has the nonlinear lower determinant estimate
with the actual mollified continuous log-density. -/
theorem weak_moment_mollify_posDef_and_det_lower
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (k : ℕ) (x : Space n) :
    (coordinateHessian (mollify k u) x).PosDef ∧
      Real.exp (mollify k (fun z => -u z + V (gradient u z)) x) ≤
        (coordinateHessian (mollify k u) x).det := by
  have hh := weak_moment_mollified_average_det_lower hLip hc hV hK hKc hpush k 0 x
  have he (f : Space n → ℝ) : translatedAverage f 0 = f := by
    funext y
    simp [translatedAverage]
  simpa only [he] using hh

/-- On each actual compact set, all genuine mollified Hessians share positive
ellipticity constants. Their dependence is through dimension, 4/kappa, and
exp(B), where B is a lower bound for the continuous log-density on the actual
radius-two enlargement of that compact set. -/
theorem weak_moment_mollified_hessian_uniformly_elliptic_on_compact
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) :
    ∃ B μ Λ : ℝ, (∀ y ∈ mollifierEnlargement S, B ≤ -u y + V (gradient u y)) ∧
      0 < μ ∧ 0 < Λ ∧ ∀ k x, x ∈ S →
        Real.exp B ≤ (coordinateHessian (mollify k u) x).det ∧
        ‖coordinateHessian (mollify k u) x‖ ≤ 4/κ ∧
        ∀ v : Space n, μ*‖v‖^2 ≤ inner ℝ v (matrixAction (coordinateHessian (mollify k u) x) v) ∧
          inner ℝ v (matrixAction (coordinateHessian (mollify k u) x) v) ≤ Λ*‖v‖^2 := by
  let f := fun y => -u y + V (gradient u y)
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV.continuous hK hKc hpush)
  have hf : Continuous f := hLip.continuous.neg.add (hV.continuous.comp hg)
  obtain ⟨B,hB⟩ := (isCompact_mollifierEnlargement hS).bddBelow_image hf.continuousOn
  have hBlo (y : Space n) (hy : y ∈ mollifierEnlargement S) : B ≤ f y :=
    hB (mem_image_of_mem _ hy)
  obtain ⟨μ,Λ,hμ,hΛ,hell⟩ := exists_uniform_ellipticity_of_det_and_norm n (4/κ) (Real.exp B) (Real.exp_pos B)
  refine ⟨B,μ,Λ,hBlo,hμ,hΛ,?_⟩
  intro k x hx
  obtain ⟨hp,hd⟩ := weak_moment_mollify_posDef_and_det_lower hLip hc hV.continuous hK hKc hpush k x
  have hdet : Real.exp B ≤ (coordinateHessian (mollify k u) x).det :=
    (Real.exp_le_exp.mpr (lower_le_mollify_on_enlargement hf hBlo k hx)).trans hd
  have hnorm := (weak_moment_mollify_hessian_upper hLip hc hV hVc hκ hstrong hK hKc hpush k x).2
  exact ⟨hdet,hnorm,hell _ hp.posSemidef hnorm hdet⟩

end KLS
end
