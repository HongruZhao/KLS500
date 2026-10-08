import KLS.NormalizedEnergyBound
import KLS.HarmonicPointwiseCalculus

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma gradient_sub_affine_eq_scaled_normalized_gradient {u : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ p : Space n) (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) (x : Space n) :
    gradient u x - (p + (x-x₀)) = ε • gradient (normalizedQuadraticError u x₀ p c ε) x := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p c
  let w := normalizedQuadraticError u x₀ p c ε
  have hq : ContDiff ℝ 1 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hw : ContDiff ℝ 1 w := contDiff_normalizedQuadraticError hu _ _ _ _
  have he : u = fun y => q y + ε * w y := funext
    (normalizedQuadraticError_reconstruction u x₀ p c hε)
  have hd := ((hq.differentiable (by norm_num) x).hasFDerivAt.add
    ((hw.differentiable (by norm_num) x).hasFDerivAt.const_mul ε)).fderiv
  change fderiv ℝ (fun y => q y + ε * w y) x = fderiv ℝ q x + ε • fderiv ℝ w x at hd
  rw [← he] at hd
  ext i
  have hi := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
  change coordinateDerivative u i x = coordinateDerivative q i x + ε * coordinateDerivative w i x at hi
  rw [coordinateDerivative_eq_gradient, coordinateDerivative_eq_gradient,
    coordinateDerivative_eq_gradient, gradient_centeredQuadratic Matrix.PosSemidef.one,
    matrixAction_one_apply] at hi
  change gradient u x i - (p + (x-x₀)) i = ε * gradient w x i
  linarith

/-- The displacement cost of the actual gradient map is exactly epsilon
squared times the local energy of the actual normalized error. -/
theorem normalized_transport_cost_identity {u χ : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ p : Space n) (c : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (∫ x, χ x ^ 2 * ‖gradient u x - (p + (x-x₀))‖ ^ 2) =
      ε ^ 2 * (∫ x, ∑ i, χ x ^ 2 *
        coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [gradient_sub_affine_eq_scaled_normalized_gradient hu x₀ p c hε x,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      ← harmonicGradientSquare_eq_norm_gradient_sq]
    simp only [harmonicGradientSquare, ← Finset.mul_sum]
    ring

/-- A proved local normalized energy bound controls the first-order scaled
transport cost with an extra factor epsilon. -/
theorem normalized_transport_cost_div_le_of_energy_bound {u χ : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ p : Space n) (c : ℝ) {ε C : ℝ} (hε : 0 < ε)
    (henergy : (∫ x, ∑ i, χ x ^ 2 *
      coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) ≤ C) :
    (∫ x, χ x ^ 2 * ‖gradient u x - (p + (x-x₀))‖ ^ 2) / ε ≤ ε * C := by
  rw [normalized_transport_cost_identity hu x₀ p c hε.ne']
  have he : ε ^ 2 * (∫ x, ∑ i, χ x ^ 2 *
      coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) / ε =
      ε * (∫ x, ∑ i, χ x ^ 2 *
      coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left henergy hε.le

/-- For a sequence with a uniform proved local energy bound and epsilon tending
to zero, its genuine first-order transport error cost tends to zero. -/
theorem normalized_transport_cost_div_tendsto_zero
    {u : ℕ → Space n → ℝ} {χ : Space n → ℝ} {ε : ℕ → ℝ} {C c : ℝ} {x₀ p : Space n}
    (hu : ∀ j, ContDiff ℝ 1 (u j)) (hε : ∀ j, 0 < ε j)
    (heps : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ j, (∫ x, ∑ i, χ x ^ 2 *
      coordinateDerivative (normalizedQuadraticError (u j) x₀ p c (ε j)) i x ^ 2) ≤ C) :
    Tendsto (fun j => (∫ x, χ x ^ 2 *
      ‖gradient (u j) x - (p + (x-x₀))‖ ^ 2) / ε j) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro j
    exact div_nonneg (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) (hε j).le
  · intro j
    exact normalized_transport_cost_div_le_of_energy_bound (hu j) x₀ p c (hε j) (henergy j)
  · simpa using heps.mul_const C

end KLS
end
