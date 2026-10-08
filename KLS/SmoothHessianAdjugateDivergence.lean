import KLS.C11HessianMollification
import KLS.HessianMetricDivergence

open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

set_option synthInstance.maxHeartbeats 100000 in
-- The actual Hessian chain rule needs additional Euclidean-space instance search.
/-- The genuine adjugate of a smooth positive Hessian has zero column
 divergence. This is a calculus identity independent of any MA equation. -/
theorem smooth_hessian_adjugate_column_divergence
    {u : Space n → ℝ} (hu : ContDiff ℝ 4 u)
    (hp : ∀ x, (coordinateHessian u x).PosDef) (x : Space n) (j : Fin n) :
    (∑ i, coordinateDerivative (fun y => (coordinateHessian u y).adjugate i j) i x) = 0 := by
  have hH := contDiff_coordinateHessian_matrix hu
  have hd : ContDiff ℝ 2 (fun y => (coordinateHessian u y).det) :=
    (MatrixCalculus.contDiff_det.of_le (by simp)).comp hH
  have hi (i : Fin n) : ContDiff ℝ 2 (fun y => (coordinateHessian u y)⁻¹ i j) :=
    contDiff_inverseHessian_entry hu hp i j
  have he (i : Fin n) : (fun y => (coordinateHessian u y).adjugate i j) =
      fun y => (coordinateHessian u y).det * (coordinateHessian u y)⁻¹ i j := by
    funext y
    rw [← det_smul_nonsing_inv_eq_adjugate (hp y).det_pos.ne']
    rfl
  have hdet (i : Fin n) : coordinateDerivative (fun y => (coordinateHessian u y).det) i x =
      (coordinateHessian u x).det *
        ((coordinateHessian u x)⁻¹ * hessianDerivative u x i).trace := by
    have hchain := (MatrixCalculus.contDiff_det.differentiable (by simp)
      (coordinateHessian u x)).hasFDerivAt.comp x ((hH.differentiable (by norm_num)) x).hasFDerivAt
    change fderiv ℝ (Matrix.det ∘ coordinateHessian u) x (EuclideanSpace.single i 1) = _
    rw [hchain.fderiv]
    change fderiv ℝ Matrix.det (coordinateHessian u x)
      (fderiv ℝ (coordinateHessian u) x (EuclideanSpace.single i 1)) = _
    rw [MatrixCalculus.fderiv_det_apply _ _ (hp x).det_pos.ne',fderiv_coordinateHessian_apply hu]
  simp_rw [he,coordinateDerivative_mul (hd.differentiable (by norm_num) x)
    ((hi _).differentiable (by norm_num) x),hdet]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc,← Finset.mul_sum]
  rw [inverseHessian_divergence_eq_trace hu hp,mul_neg]
  ring

/-- The smooth adjugate column identity gives the actual distributional
 divergence identity against each compact C1 test. -/
theorem smooth_hessian_adjugate_integral_column
    {u ψ : Space n → ℝ} (hu : ContDiff ℝ 4 u)
    (hp : ∀ x, (coordinateHessian u x).PosDef)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, (coordinateHessian u x).adjugate i j * coordinateDerivative ψ i x) = 0 := by
  have hA : ContDiff ℝ 2 (fun x => (coordinateHessian u x).adjugate) :=
    (MatrixCalculus.contDiff_adjugate.of_le (by simp)).comp (contDiff_coordinateHessian_matrix hu)
  have hAi (i : Fin n) : ContDiff ℝ 1 (fun x => (coordinateHessian u x).adjugate i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).of_le (by norm_num)
  have hint (i : Fin n) : Integrable
      (fun x => coordinateDerivative (fun y => (coordinateHessian u y).adjugate i j) i x * ψ x) :=
    (((contDiff_coordinateDerivative (hAi i) (m := 0) (by norm_num) i).continuous).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hibp (i : Fin n) : (∫ x, (coordinateHessian u x).adjugate i j * coordinateDerivative ψ i x) =
      -(∫ x, coordinateDerivative (fun y => (coordinateHessian u y).adjugate i j) i x * ψ x) := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint i)
      (((hAi i).continuous.mul (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i).mul_left)
      (((hAi i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => (hAi i).differentiable (by norm_num) x)
      (fun x _ => hψ.differentiable (by norm_num) x)
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ => hint i)]
  have he : (fun x => ∑ i, coordinateDerivative (fun y => (coordinateHessian u y).adjugate i j) i x*ψ x) = 0 := by
    funext x
    rw [← Finset.sum_mul,smooth_hessian_adjugate_column_divergence hu hp,zero_mul]
    rfl
  rw [he]
  simp

end KLS
end
