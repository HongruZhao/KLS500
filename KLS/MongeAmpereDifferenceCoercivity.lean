import KLS.LogDetQuantitativeConcavity
import KLS.MomentMapFiniteDifference

open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The sum of both tangent gaps controls both actual matrix increments. -/
theorem log_det_centered_frobenius_gap {H P M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hP : P.PosDef) (hM : M.PosDef) {K : ℝ} (hK : 0 < K)
    (hHu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef)
    (hPu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P).PosSemidef)
    (hMu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - M).PosSemidef) :
    ((K⁻¹) ^ 2 / 2) * (matrixFrobeniusSq (P - H) + matrixFrobeniusSq (M - H)) ≤
      (H⁻¹ * (P + M - (2 : ℝ) • H)).trace -
        (Real.log P.det + Real.log M.det - 2 * Real.log H.det) := by
  have hp := log_det_tangent_frobenius_gap hH hP hK hHu hPu
  have hm := log_det_tangent_frobenius_gap hH hM hK hHu hMu
  have he : (H⁻¹ * (P + M - (2 : ℝ) • H)).trace =
      (H⁻¹ * (P - H)).trace + (H⁻¹ * (M - H)).trace := by
    rw [show P + M - (2 : ℝ) • H = (P - H) + (M - H) by module,
      Matrix.mul_add, Matrix.trace_add]
  rw [he]
  nlinarith

/-- The three literal MA identities and actual convex target give a
coercive centered difference inequality. This is matrix algebra at three
points; no differentiability or weak energy of a source is assumed. -/
theorem mongeAmpere_three_point_coercivity
    {H P M : Matrix (Fin n) (Fin n) ℝ} {V : Space n → ℝ}
    (hH : H.PosDef) (hP : P.PosDef) (hM : M.PosDef) {K : ℝ} (hK : 0 < K)
    (hHu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef)
    (hPu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P).PosSemidef)
    (hMu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - M).PosSemidef)
    (hV : Differentiable ℝ V) (hconv : ConvexOn ℝ univ V)
    (r₀ rplus rminus : ℝ) (p₀ pplus pminus : Space n)
    (hMA₀ : Real.log H.det = -r₀ + V p₀)
    (hMAplus : Real.log P.det = -rplus + V pplus)
    (hMAminus : Real.log M.det = -rminus + V pminus) :
    ((K⁻¹) ^ 2 / 2) * (matrixFrobeniusSq (P - H) + matrixFrobeniusSq (M - H)) ≤
      (H⁻¹ * (P + M - (2 : ℝ) • H)).trace -
        fderiv ℝ V p₀ (pplus + pminus - (2 : ℝ) • p₀) + (rplus + rminus - 2 * r₀) := by
  have hp := convex_supporting_fderiv hconv hV p₀ pplus
  have hm := convex_supporting_fderiv hconv hV p₀ pminus
  have hlin : fderiv ℝ V p₀ (pplus + pminus - (2 : ℝ) • p₀) =
      fderiv ℝ V p₀ (pplus - p₀) + fderiv ℝ V p₀ (pminus - p₀) := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    ring
  have htarget : fderiv ℝ V p₀ (pplus + pminus - (2 : ℝ) • p₀) ≤
      V pplus + V pminus - 2 * V p₀ := by rw [hlin]; linarith
  have hgap := log_det_centered_frobenius_gap hH hP hM hK hHu hPu hMu
  rw [hMA₀, hMAplus, hMAminus] at hgap
  linarith

/-- Specialization to the actual Hessian, gradient and centered potential
increment. Only the stated three pointwise MA data are consumed. -/
theorem mongeAmpere_centeredDifference_coercivity_at {u V : Space n → ℝ}
    (hV : Differentiable ℝ V) (hconv : ConvexOn ℝ univ V)
    (x h : Space n) {K : ℝ} (hK : 0 < K)
    (h₀ : (coordinateHessian u x).PosDef)
    (hplus : (coordinateHessian u (x + h)).PosDef)
    (hminus : (coordinateHessian u (x - h)).PosDef)
    (hU₀ : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - coordinateHessian u x).PosSemidef)
    (hUplus : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - coordinateHessian u (x + h)).PosSemidef)
    (hUminus : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - coordinateHessian u (x - h)).PosSemidef)
    (hMA₀ : Real.log (coordinateHessian u x).det = -u x + V (gradient u x))
    (hMAplus : Real.log (coordinateHessian u (x + h)).det = -u (x + h) + V (gradient u (x + h)))
    (hMAminus : Real.log (coordinateHessian u (x - h)).det = -u (x - h) + V (gradient u (x - h))) :
    ((K⁻¹) ^ 2 / 2) * (matrixFrobeniusSq (coordinateHessian u (x + h) - coordinateHessian u x) +
        matrixFrobeniusSq (coordinateHessian u (x - h) - coordinateHessian u x)) ≤
      ((coordinateHessian u x)⁻¹ *
        (coordinateHessian u (x + h) + coordinateHessian u (x - h) -
          (2 : ℝ) • coordinateHessian u x)).trace -
      fderiv ℝ V (gradient u x)
        (gradient u (x + h) + gradient u (x - h) - (2 : ℝ) • gradient u x) +
      symmetricSecondDifference u h x :=
  mongeAmpere_three_point_coercivity h₀ hplus hminus hK hU₀ hUplus hUminus hV hconv
    (u x) (u (x + h)) (u (x - h)) (gradient u x) (gradient u (x + h)) (gradient u (x - h))
    hMA₀ hMAplus hMAminus

end KLS
end
