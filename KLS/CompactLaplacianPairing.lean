import KLS.FirstOrderTransportBound

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma integral_inner_gradient_eq_neg_laplacian_pairing {h φ : Space n → ℝ}
    (hh : ContDiff ℝ 1 h) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, inner ℝ (gradient φ x) (gradient h x)) =
      -(∫ x, h x * coordinateLaplacian φ x) := by
  have hleft (i : Fin n) : Integrable (fun x => coordinateDerivative φ i x * coordinateDerivative h i x) :=
    ((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous.mul
      (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hright (i : Fin n) : Integrable (fun x => coordinateHessian φ x i i * h x) :=
    ((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i i).continuous.mul hh.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateHessian hc i i).mul_right
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_mul_coordinateDerivative_of_hasCompactSupport_left
      (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i) hh
      (hasCompactSupport_coordinateDerivative hc i) i)
  change (∑ i, ∫ x, coordinateDerivative φ i x * coordinateDerivative h i x) =
    ∑ i, -(∫ x, coordinateHessian φ x i i * h x) at hsum
  rw [← integral_finsetSum _ (fun i _ => hleft i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hright i)] at hsum
  have he : (fun x => ∑ i, coordinateHessian φ x i i * h x) =
      (fun x => h x * coordinateLaplacian φ x) := by
    funext x
    simp only [coordinateLaplacian, Finset.mul_sum, mul_comm]
  rw [he] at hsum
  convert hsum using 2
  funext x
  simp only [coordinateDerivative_eq_gradient, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_comm]

lemma integral_cutoff_norm_gradient_sq_eq_coordinate_energy (χ h : Space n → ℝ) :
    (∫ x, χ x ^ 2 * ‖gradient h x‖ ^ 2) =
      (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← harmonicGradientSquare_eq_norm_gradient_sq]
    simp only [harmonicGradientSquare, Finset.mul_sum]

lemma abs_sub_quadratic_le_of_normalized_bound {u : Space n → ℝ}
    {c ε M : ℝ} (hε : 0 < ε) {x : Space n}
    (hbound : |normalizedQuadraticError u 0 0 c ε x| ≤ M) :
    |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ ε * M := by
  rw [normalizedQuadraticError, abs_div, abs_of_pos hε, div_le_iff₀ hε] at hbound
  simpa only [mul_comm] using hbound

end KLS
end
