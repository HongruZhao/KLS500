import KLS.LocalLipschitzWeakDerivative

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Genuine iterated weak derivatives commute. Only smooth compact test
functions are differentiated twice; the source need not be smooth. -/
theorem weak_mixed_coordinateDerivatives_commute
    {f fi fj fij fji : Space n → ℝ} {i j : Fin n}
    (hi : HasLocalWeakCoordinateDerivative f fi i)
    (hj : HasLocalWeakCoordinateDerivative f fj j)
    (hij : HasLocalWeakCoordinateDerivative fi fij j)
    (hji : HasLocalWeakCoordinateDerivative fj fji i)
    (hijl : LocallyIntegrable fij volume) (hjil : LocallyIntegrable fji volume) :
    fij =ᵐ[volume] fji := by
  apply ae_eq_of_integral_contDiff_smul_eq hijl hjil
  intro ψ hψ hc
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hd (k : Fin n) : ContDiff ℝ 1 (coordinateDerivative ψ k) :=
    contDiff_coordinateDerivative hψ (by simp) k
  have he : coordinateDerivative (coordinateDerivative ψ j) i =
      coordinateDerivative (coordinateDerivative ψ i) j := by
    funext x
    exact ((coordinateHessian_symmetric (hψ.of_le (by simp)) x).apply j i)
  have ha := hi (coordinateDerivative ψ j) (hd j) (hasCompactSupport_coordinateDerivative hc j)
  have hb := hj (coordinateDerivative ψ i) (hd i) (hasCompactSupport_coordinateDerivative hc i)
  have hA := hij ψ hψ1 hc
  have hB := hji ψ hψ1 hc
  rw [he] at ha
  have hfinal : (∫ x, fij x * ψ x) = ∫ x, fji x * ψ x := by linarith
  simpa only [smul_eq_mul, mul_comm] using hfinal

end KLS
end
