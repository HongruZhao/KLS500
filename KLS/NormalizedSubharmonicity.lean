import KLS.NormalizedMongeAmpereViscosity
import KLS.MatrixLogDetTangent
import KLS.ContinuousViscosityDistribution

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma log_lower_of_abs_sub_one_le_sq {a ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (ha : |a - 1| ≤ ε ^ 2) : -2 * ε ^ 2 ≤ Real.log a := by
  have he : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have ha0 : 0 < a := by have h := (abs_le.mp ha).1; nlinarith
  have hai : a⁻¹ ≤ 1 + 2 * ε ^ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha0).mpr
    have h := (abs_le.mp ha).1
    nlinarith [mul_nonneg (show 0 ≤ a - (1 - ε ^ 2) by linarith)
      (show 0 ≤ 1 + 2 * ε ^ 2 by positivity)]
  have hlog := Real.one_sub_inv_le_log_of_pos ha0
  linarith

/-- Unlike the determinant Taylor estimate, this genuine one-sided Laplace
bound places no size restriction on the touching test's Hessian. -/
theorem normalized_mongeAmpere_upper_test_laplacian_unrestricted
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    {x : Space n} (hdensity : |f x - 1| ≤ ε ^ 2)
    (hcontact : normalizedQuadraticError u x₀ p c ε x = ψ x)
    (htouch : ∀ᶠ y in 𝓝 x, normalizedQuadraticError u x₀ p c ε y ≤ ψ y) :
    -2 * ε ≤ coordinateLaplacian ψ x := by
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
  have hdet := det_ge_density_of_convex_c2_upper_touch hu huc hf.continuousAt hMA
    hΦ.contDiffAt hc ht
  have hfpos : 0 < f x := by
    have hh := (abs_le.mp hdensity).1
    nlinarith [sq_nonneg ε]
  have hpd : (coordinateHessian Φ x).PosDef :=
    hpsd.posDef_iff_det_ne_zero.mpr (hfpos.trans_le hdet).ne'
  have htrace := log_det_le_trace_sub_dimension hpd
  have hlog := (log_lower_of_abs_sub_one_le_sq hε.le hεhalf hdensity).trans
    (Real.log_le_log hfpos hdet)
  have hH : coordinateHessian Φ x = 1 + ε • coordinateHessian ψ x :=
    coordinateHessian_quadratic_add_harmonic hψ x₀ p c ε x
  rw [hH] at hlog
  rw [hH, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] at htrace
  change -2 * ε ≤ (coordinateHessian ψ x).trace
  apply (mul_le_mul_iff_right₀ hε).mp
  simp only [smul_eq_mul, Fintype.card_fin] at htrace
  nlinarith

end KLS
end
