import KLS.ScaledDeterminantRemainder

/-! Quantitative linearization of the actual weak Monge--Ampere equation.
Only smooth touching tests have Hessians. The normalized error itself need not
be twice differentiable. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual difference from a unit-Hessian quadratic, divided by epsilon. -/
def normalizedQuadraticError (u : Space n → ℝ) (x₀ p : Space n) (c ε : ℝ) : Space n → ℝ :=
  fun x => (u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x) / ε

lemma normalizedQuadraticError_reconstruction (u : Space n → ℝ)
    (x₀ p : Space n) (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x : Space n) :
    u x = centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c x +
      ε * normalizedQuadraticError u x₀ p c ε x := by
  dsimp [normalizedQuadraticError]
  field_simp
  ring

/-- Every smooth upper test of the normalized actual solution satisfies an
approximate subharmonic inequality, with an explicit error tending to zero. -/
theorem normalized_mongeAmpere_upper_test_laplacian_bound
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 < B) (hsmall : |ε * B| ≤ 1 / 2)
    {x : Space n} (hH : ‖matrixAction (coordinateHessian ψ x)‖ ≤ B)
    (hdensity : |f x - 1| ≤ ε ^ 2)
    (hcontact : normalizedQuadraticError u x₀ p c ε x = ψ x)
    (htouch : ∀ᶠ y in 𝓝 x, normalizedQuadraticError u x₀ p c ε y ≤ ψ y) :
    -(1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε ≤ coordinateLaplacian ψ x := by
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
  have hdet := det_ge_density_of_convex_c2_upper_touch hu huc hf.continuousAt hMA
    hΦ.contDiffAt hc ht
  rw [show coordinateHessian Φ x = 1 + ε • coordinateHessian ψ x from
    coordinateHessian_quadratic_add_harmonic hψ x₀ p c ε x] at hdet
  have hr := determinant_remainder_bound_of_norm_le hB
    ((elementwise_matrix_norm_le_matrixAction_norm _).trans hH)
    (hsmall.trans (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have hrhi := (abs_le.mp hr).2
  have hflo := (abs_le.mp hdensity).1
  change -(1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε ≤
    (coordinateHessian ψ x).trace
  apply (mul_le_mul_iff_right₀ hε).mp
  nlinarith

/-- Every smooth lower test satisfies the other approximate harmonic
inequality. Its admissible positive Hessian is derived from the small scale. -/
theorem normalized_mongeAmpere_lower_test_laplacian_bound
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiff ℝ 2 ψ) (x₀ p : Space n) (c : ℝ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 < B) (hsmall : |ε * B| ≤ 1 / 2)
    {x : Space n} (hH : ‖matrixAction (coordinateHessian ψ x)‖ ≤ B)
    (hdensity : |f x - 1| ≤ ε ^ 2)
    (hcontact : normalizedQuadraticError u x₀ p c ε x = ψ x)
    (htouch : ∀ᶠ y in 𝓝 x, ψ y ≤ normalizedQuadraticError u x₀ p c ε y) :
    coordinateLaplacian ψ x ≤ (1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c
  let Φ : Space n → ℝ := fun y => q y + ε * ψ y
  have hΦ : ContDiff ℝ 2 Φ :=
    ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)).add (contDiff_const.mul hψ)
  have hc : u x = Φ x := by
    rw [normalizedQuadraticError_reconstruction u x₀ p c hε.ne' x, hcontact]
  have ht : ∀ᶠ y in 𝓝 x, Φ y ≤ u y := by
    filter_upwards [htouch] with y hy
    rw [normalizedQuadraticError_reconstruction u x₀ p c hε.ne' y]
    dsimp [Φ, q]
    gcongr
  have hΦH : coordinateHessian Φ x = 1 + ε • coordinateHessian ψ x :=
    coordinateHessian_quadratic_add_harmonic hψ x₀ p c ε x
  have hpos : (coordinateHessian Φ x).PosSemidef := by
    rw [hΦH]
    exact (posDef_one_add_smul_of_scaled_operator_bound
      (coordinateHessian_symmetric hψ x) hB hH hsmall).posSemidef
  have hdet := det_le_density_of_c2_semidefinite_lower_touch hu huc hf.continuousAt
    (hf0 x) hMA hΦ.contDiffAt hpos hc ht
  rw [hΦH] at hdet
  have hr := determinant_remainder_bound_of_norm_le hB
    ((elementwise_matrix_norm_le_matrixAction_norm _).trans hH)
    (hsmall.trans (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have hrlo := (abs_le.mp hr).1
  have hfhi := (abs_le.mp hdensity).2
  change (coordinateHessian ψ x).trace ≤
    (1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε
  apply (mul_le_mul_iff_right₀ hε).mp
  nlinarith

end KLS
end
