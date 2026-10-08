import KLS.LocalAlexandrovUpperTests
import KLS.NormalizedSubharmonicDistribution

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A local Alexandrov equation and a lower bound on its log density control
all normalized upper tests, with no Hessian size restriction. -/
theorem normalized_upper_test_laplacian_of_local_log_density
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {x : Space n} (hf : ContinuousAt f x) (hfpos : 0 < f x)
    {U : Set (Space n)} (hU : U ∈ 𝓝 x)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ U →
      volume (convexSubgradientImage u S) = ∫⁻ y in S, ENNReal.ofReal (f y) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε)
    (hcontact : normalizedQuadraticError u x₀ p c ε x = ψ x)
    (htouch : ∀ᶠ y in 𝓝 x, normalizedQuadraticError u x₀ p c ε y ≤ ψ y) :
    Real.log (f x) ≤ ε * coordinateLaplacian ψ x := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c
  let Φ : Space n → ℝ := fun y => q y + ε * ψ y
  have hΦ : ContDiff ℝ 2 Φ :=
    ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)).add (contDiff_const.mul hψ)
  have hc : u x = Φ x := by
    rw [normalizedQuadraticError_reconstruction u x₀ p c hε.ne' x, hcontact]
  have ht : ∀ᶠ y in 𝓝 x, u y ≤ Φ y := by
    filter_upwards [htouch] with y hy
    rw [normalizedQuadraticError_reconstruction u x₀ p c hε.ne' y]
    dsimp [Φ, q]
    gcongr
  have hpsd := coordinateHessian_posSemidef_of_convex_upper_touch huc hΦ.contDiffAt hc ht
  have hdet := det_ge_density_of_convex_c2_upper_touch_local hu huc hf hU hMA hΦ.contDiffAt hc ht
  have hpd : (coordinateHessian Φ x).PosDef :=
    hpsd.posDef_iff_det_ne_zero.mpr (hfpos.trans_le hdet).ne'
  have htrace := log_det_le_trace_sub_dimension hpd
  have hlog := Real.log_le_log hfpos hdet
  have hH : coordinateHessian Φ x = 1 + ε • coordinateHessian ψ x :=
    coordinateHessian_quadratic_add_harmonic hψ x₀ p c ε x
  rw [hH] at hlog
  rw [hH, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] at htrace
  change Real.log (f x) ≤ ε * (coordinateHessian ψ x).trace
  simp only [smul_eq_mul, Fintype.card_fin] at htrace
  linarith

theorem subharmonicNormalizedError_upper_test_of_local_log_density (hn : 0 < n)
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {x : Space n} (hf : ContinuousAt f x) (hfpos : 0 < f x)
    {U : Set (Space n)} (hU : U ∈ 𝓝 x)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ U →
      volume (convexSubgradientImage u S) = ∫⁻ y in S, ENNReal.ofReal (f y) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hlog : -2 * ε ^ 2 ≤ Real.log (f x))
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
  have hb := normalized_upper_test_laplacian_of_local_log_density hu huc hf hfpos hU hMA hρ
    x₀ p c hε hcontact htouch
  change Real.log (f x) ≤ ε * coordinateLaplacian (fun y => ψ y + (-2 * ε) *
    centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 y + d) x at hb
  rw [coordinateLaplacian_add_scalar_quadratic_const hψ] at hb
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul : 0 ≤ ε * coordinateLaplacian ψ x := by nlinarith [sq_nonneg ε]
  exact nonneg_of_mul_nonneg_right hmul hε

end KLS
end
