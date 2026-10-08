import KLS.WeakMomentGradientLipschitz

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual normalized nonnegative mollifier preserves any global quadratic
upper bound for symmetric finite differences. -/
theorem symmetricSecondDifference_mollify_le
    {u : Space n → ℝ} (hu : Continuous u) {A : ℝ}
    (hb : ∀ h x, symmetricSecondDifference u h x ≤ A * ‖h‖ ^ 2)
    (k : ℕ) (h x : Space n) :
    symmetricSecondDifference (mollify k u) h x ≤ A * ‖h‖ ^ 2 := by
  have hip := integrable_mollifier_left hu k (x+h)
  have him := integrable_mollifier_left hu k (x-h)
  have hi0 := (integrable_mollifier_left hu k x).const_mul 2
  have hiR : Integrable (fun y => mollifierKernel n k y * (A * ‖h‖ ^ 2)) :=
    (mollifierBump n k).integrable_normed.mul_const _
  unfold symmetricSecondDifference
  rw [mollify_eq_integral_kernel_left,mollify_eq_integral_kernel_left,
    mollify_eq_integral_kernel_left,← integral_add hip him,← integral_const_mul,
    ← integral_sub (f := fun y => mollifierKernel n k y * u (x+h-y) +
      mollifierKernel n k y * u (x-h-y)) (hip.add him) hi0]
  calc
    _ ≤ ∫ y, mollifierKernel n k y * (A * ‖h‖ ^ 2) := by
      apply integral_mono ((hip.add him).sub hi0) hiR
      intro y
      have hh := mul_le_mul_of_nonneg_left (hb h (x-y))
        ((mollifierBump n k).nonneg_normed (μ := volume) y)
      have hep : x+h-y = (x-y)+h := by abel
      have hem : x-h-y = (x-y)-h := by abel
      change mollifierKernel n k y * u (x+h-y) + mollifierKernel n k y * u (x-h-y) -
        2 * (mollifierKernel n k y * u (x-y)) ≤ mollifierKernel n k y * (A * ‖h‖^2)
      rw [hep,hem]
      dsimp [symmetricSecondDifference,mollifierKernel] at *
      nlinarith
    _ = _ := by
      rw [integral_mul_const]
      simp only [mollifierKernel,(mollifierBump n k).integral_normed,one_mul]

/-- The genuine second derivative of a smooth function is bounded by its
actual unscaled finite-difference bound, using the Taylor limit. -/
theorem secondFrechet_le_of_secondDifference_bound
    {u : Space n → ℝ} (hu : ContDiff ℝ 2 u) {A : ℝ}
    (hb : ∀ h x, symmetricSecondDifference u h x ≤ A * ‖h‖ ^ 2)
    (x v : Space n) : fderiv ℝ (fderiv ℝ u) x v v ≤ A * ‖v‖ ^ 2 := by
  apply le_of_tendsto (tendsto_symmetricSecondDifference_directional hu x v)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hh := hb (t • v) x
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht0)).mpr
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hh
  convert hh using 1
  ring

/-- Uniform coordinate and quadratic Hessian bounds for every actual
mollification of the original weak moment potential. -/
theorem weak_moment_mollify_hessian_upper
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (k : ℕ) (x : Space n) :
    (∀ v : Space n, fderiv ℝ (fderiv ℝ (mollify k u)) x v v ≤ (4/κ)*‖v‖^2) ∧
      ‖coordinateHessian (mollify k u) x‖ ≤ 4/κ := by
  have hu : ContDiff ℝ 2 (mollify k u) :=
    (mollify_contDiff hLip.continuous.locallyIntegrable k).of_le (by simp)
  have hbound (h y : Space n) : symmetricSecondDifference u h y ≤ (4/κ)*‖h‖^2 := by
    convert weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target
      hLip hc hV hVc hκ hstrong hK hKc hpush h y using 1
    ring
  have hsecond := secondFrechet_le_of_secondDifference_bound hu
    (symmetricSecondDifference_mollify_le hLip.continuous hbound k) x
  refine ⟨hsecond,?_⟩
  have hpos : (coordinateHessian (mollify k u) x).PosDef := by
    have hh := (weak_moment_mollified_average_det_lower hLip hc hV.continuous hK hKc hpush k 0 x).1
    have he : translatedAverage (mollify k u) 0 = mollify k u := by
      funext y
      simp [translatedAverage]
    rwa [he] at hh
  have hpsd := hpos.posSemidef
  have hdiag (i : Fin n) : coordinateHessian (mollify k u) x i i ≤ 4/κ := by
    have hh := hsecond (EuclideanSpace.single i 1)
    rw [← coordinateHessian_quadratic_eq hu] at hh
    simpa using hh
  apply (Matrix.norm_le_iff (by positivity : (0 : ℝ) ≤ 4/κ)).mpr
  intro i j
  have hcs : (coordinateHessian (mollify k u) x i j)^2 ≤
      coordinateHessian (mollify k u) x i i * coordinateHessian (mollify k u) x j j := by
    simpa [pow_two] using hpos.star_dotProduct_mulVec_mul_le (Pi.single i 1) (Pi.single j 1)
  have hp := mul_le_mul (hdiag i) (hdiag j) (hpsd.diag_nonneg : 0 ≤ coordinateHessian (mollify k u) x j j)
    (by positivity : (0 : ℝ) ≤ 4/κ)
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 4/κ)).mp
  rw [sq_abs]
  nlinarith

end KLS
end
