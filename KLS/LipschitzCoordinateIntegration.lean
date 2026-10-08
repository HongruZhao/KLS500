import KLS.WeakMomentAeEllipticity
import KLS.WeakDerivativeMollification

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual derivatives of a Lipschitz scalar function satisfy integration by
 parts against every compact C1 test; no global L2 condition is imposed. -/
theorem lipschitz_integral_coordinateDerivative_mul
    {f ψ : Space n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, coordinateDerivative f i x * ψ x) = -(∫ x, f x * coordinateDerivative ψ i x) := by
  obtain ⟨D,hψLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by norm_num)
  have hh := hf.integral_lineDeriv_mul_eq (μ := (volume : Measure (Space n)))
    hψLip hc (EuclideanSpace.single i 1)
  have hl : (∫ x, lineDeriv ℝ f x (EuclideanSpace.single i 1)*ψ x) =
      ∫ x, coordinateDerivative f i x*ψ x := by
    apply integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
    rfl
  have hr : (∫ x, lineDeriv ℝ ψ x (-EuclideanSpace.single i 1)*f x) =
      -(∫ x, f x*coordinateDerivative ψ i x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [((hψ.differentiable (by norm_num)) x).lineDeriv_eq_fderiv,map_neg]
      change -coordinateDerivative ψ i x*f x = -(f x*coordinateDerivative ψ i x)
      ring
  rwa [hl,hr] at hh

/-- Coordinate projections preserve a vector-valued Lipschitz constant. -/
lemma lipschitz_coordinate_component {g : Space n → Space n} {L : ℝ≥0}
    (hg : LipschitzWith L g) (i : Fin n) : LipschitzWith L (fun x => g x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (PiLp.norm_apply_le (g x-g y) i).trans (hg.norm_sub_le x y)
  simpa only [dist_eq_norm,PiLp.sub_apply] using hh

/-- Actual coordinate derivatives of a C1,1 potential are Lipschitz. -/
lemma lipschitz_coordinateDerivative_of_gradient_lipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u)) (i : Fin n) :
    LipschitzWith G (coordinateDerivative u i) := by
  have heq : coordinateDerivative u i = fun x => gradient u x i := by
    funext x
    exact coordinateDerivative_eq_gradient u i x
  rw [heq]
  exact lipschitz_coordinate_component hG i

end KLS
end
