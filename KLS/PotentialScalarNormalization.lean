import KLS.GradientAffineRescaling

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma det_inv_smul_one_ne_zero {r : ℝ} (hr : r ≠ 0) :
    (r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0 := by
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (inv_ne_zero hr)

/-- The actual coordinate normalization x maps to (x-center)/r. -/
def scalarNormalizationEquiv (x₀ : Space n) (r : ℝ) (hr : r ≠ 0) : Space n ≃ᴬ[ℝ] Space n :=
  affineMatrixEquiv (r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) (-r⁻¹ • x₀)
    (det_inv_smul_one_ne_zero hr)

lemma scalarNormalizationEquiv_apply (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    scalarNormalizationEquiv x₀ r hr x = r⁻¹ • (x - x₀) := by
  change matrixAction (r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) x + (-r⁻¹ • x₀) = _
  simp only [matrixAction_smul_scalar, matrixAction_one_apply, smul_sub, neg_smul]
  abel

lemma scalarNormalizationEquiv_symm_apply (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    (scalarNormalizationEquiv x₀ r hr).symm y = x₀ + r • y := by
  apply (scalarNormalizationEquiv x₀ r hr).symm_apply_eq.mpr
  rw [scalarNormalizationEquiv_apply]
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]

lemma scalarNormalizationEquiv_inverse_identity (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    x₀ + r • scalarNormalizationEquiv x₀ r hr x = x := by
  rw [scalarNormalizationEquiv_apply, smul_smul, mul_inv_cancel₀ hr, one_smul]
  abel

/-- Both the source and target normalized measures acquire this same
additive logarithmic Jacobian constant. -/
def scalarNormalizedPotential (u : Space n → ℝ) (x₀ : Space n) (r : ℝ) : Space n → ℝ :=
  fun y => u (x₀ + r • y) - Real.log |r ^ n|

lemma map_potentialMeasure_scalarNormalization {u : Space n → ℝ} (hu : Measurable u)
    (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) :
    (potentialMeasure u).map (scalarNormalizationEquiv x₀ r hr) =
      potentialMeasure (scalarNormalizedPotential u x₀ r) := by
  rw [scalarNormalizationEquiv, map_potentialMeasure_affineMatrixEquiv hu]
  congr 1
  funext y
  change u ((scalarNormalizationEquiv x₀ r hr).symm y) -
      Real.log |(r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).det⁻¹| = _
  rw [scalarNormalizationEquiv_symm_apply]
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, inv_pow, inv_inv,
    scalarNormalizedPotential]

lemma map_restrict_scalarNormalization (μ : Measure (Space n)) (K : Set (Space n))
    (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) :
    (μ.restrict K).map (scalarNormalizationEquiv x₀ r hr) =
      (μ.map (scalarNormalizationEquiv x₀ r hr)).restrict ((scalarNormalizationEquiv x₀ r hr) '' K) :=
  map_restrict_affineMatrixEquiv μ _ _ _ K

lemma scalarNormalizedPotential_quadratic_temperature
    (u : Space n → ℝ) (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    scalarNormalizedPotential u x₀ r y =
      r ^ 2 * quadraticallyRescaledPotential u x₀ p a r y + r * inner ℝ p y +
        (a - Real.log |r ^ n|) := by
  rw [scalarNormalizedPotential, quadratic_rescaling_reconstruction u x₀ p a hr y]
  ring

end KLS
end
