import KLS.NormalizedSubharmonicity

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A vanishing quadratic correction makes the actual normalized error
subharmonic on any region where the density error is at most epsilon squared. -/
def subharmonicNormalizedError (u : Space n → ℝ) (x₀ p : Space n) (c ε : ℝ) : Space n → ℝ :=
  fun x => normalizedQuadraticError u x₀ p c ε x +
    (2 * ε) * centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 x

lemma continuous_subharmonicNormalizedError {u : Space n → ℝ} (hu : Continuous u)
    (x₀ p : Space n) (c ε : ℝ) : Continuous (subharmonicNormalizedError u x₀ p c ε) := by
  unfold subharmonicNormalizedError normalizedQuadraticError
  exact ((hu.sub (continuous_centeredQuadratic _ _ _ _)).div_const ε).add
    (continuous_const.mul (continuous_centeredQuadratic _ _ _ _))

theorem subharmonicNormalizedError_upper_test (hn : 0 < n)
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    {x : Space n} (hdensity : |f x - 1| ≤ ε ^ 2)
    (hm : IsLocalMax (fun y => subharmonicNormalizedError u x₀ p c ε y - ψ y) x) :
    0 ≤ coordinateLaplacian ψ x := by
  let d := subharmonicNormalizedError u x₀ p c ε x - ψ x
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0
  let ρ : Space n → ℝ := fun y => ψ y + (-2 * ε) * q y + d
  have hρ : ContDiff ℝ 2 ρ :=
    (hψ.add (contDiff_const.mul ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)))).add contDiff_const
  have hcontact : normalizedQuadraticError u x₀ p c ε x = ρ x := by
    dsimp [ρ, d, subharmonicNormalizedError, q]
    ring
  have htouch : ∀ᶠ y in 𝓝 x, normalizedQuadraticError u x₀ p c ε y ≤ ρ y := by
    filter_upwards [hm] with y hy
    dsimp [subharmonicNormalizedError] at hy
    dsimp [ρ, d, subharmonicNormalizedError, q]
    linarith
  have hb := normalized_mongeAmpere_upper_test_laplacian_unrestricted hu huc hf hMA hρ
    x₀ p c hε hεhalf hdensity hcontact htouch
  change -2 * ε ≤ coordinateLaplacian (fun y => ψ y + (-2 * ε) *
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 y + d) x at hb
  rw [coordinateLaplacian_add_scalar_quadratic_const hψ] at hb
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The genuine weak Monge--Ampere equation gives a distribution inequality
for the actual corrected normalized error, with no Hessian input. -/
theorem integral_subharmonicNormalizedError_mul_laplacian_nonneg (hn : 0 < n)
    {u f : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (x₀ p : Space n) (c : ℝ) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    {a : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hdensity : ∀ x ∈ closedBall a R, |f x - 1| ≤ ε ^ 2)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball a r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, subharmonicNormalizedError u x₀ p c ε x * coordinateLaplacian φ x :=
  integral_mul_laplacian_nonneg_of_continuous_upper_tests_on_ball hr hrR
    (continuous_subharmonicNormalizedError hu _ _ _ _).continuousOn
    (fun x hx ψ hψ hm => subharmonicNormalizedError_upper_test hn hu huc hf hMA
      (hψ.of_le (by simp)) x₀ p c hε hεhalf (hdensity x hx) hm) hφ hφc hφs hφ0

/-- The distribution inequality for the original finite-mass weak moment map. -/
theorem moment_integral_subharmonicNormalizedError_mul_laplacian_nonneg (hn : 0 < n)
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ p : Space n) (c : ℝ) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    {a : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hdensity : ∀ x ∈ closedBall a R, |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball a r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, subharmonicNormalizedError u x₀ p c ε x * coordinateLaplacian φ x :=
  integral_subharmonicNormalizedError_mul_laplacian_nonneg hn hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush)
    (fun _S hS => subgradient_volume_eq_lintegral_real_moment_density hLip hc hV.measurable
      hK.measurableSet hKc hpush hS) x₀ p c hε hεhalf hr hrR hdensity hφ hφc hφs hφ0

end KLS
end
