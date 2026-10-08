import KLS.LipschitzCoordinateIntegration

open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ContDiff NNReal Convolution
noncomputable section
namespace KLS
variable {n : ℕ}

/-- For a globally Lipschitz function, actual differentiation commutes with
 convolution by a compact C1 kernel, with no global L2 hypotheses. -/
theorem lipschitz_coordinateDerivative_scalarConvolution
    {f κ : Space n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) (i : Fin n) (a : Space n) :
    coordinateDerivative (scalarConvolution f κ) i a = scalarConvolution (coordinateDerivative f i) κ a := by
  rw [coordinateDerivative_scalarConvolution hf.continuous.locallyIntegrable hκ hc]
  have ht : ContDiff ℝ 1 (fun y => κ (a-y)) := hκ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (fun y => κ (a-y)) := hc.comp_homeomorph (Homeomorph.subLeft a)
  have he := lipschitz_integral_coordinateDerivative_mul hf ht htc i
  have hl : (∫ y, f y*coordinateDerivative (fun z => κ (a-z)) i y) =
      -(scalarConvolution f (coordinateDerivative κ i) a) := by
    unfold scalarConvolution
    rw [convolution_def,← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by norm_num))]
      simp
  rw [hl,neg_neg] at he
  exact he.symm

/-- Actual coordinate differentiation commutes with each actual mollifier. -/
theorem lipschitz_coordinateDerivative_mollify
    {f : Space n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (k : ℕ) (i : Fin n) :
    coordinateDerivative (mollify k f) i = mollify k (coordinateDerivative f i) := by
  funext x
  exact lipschitz_coordinateDerivative_scalarConvolution hf
    ((mollifierKernel_contDiff k).of_le (by simp)) (mollifierKernel_hasCompactSupport k) i x

/-- The actual Hessian of each mollification equals entrywise mollification
 of the actual iterated-derivative Hessian of the C1,1 potential. -/
theorem coordinateHessian_mollify_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (k : ℕ) (x : Space n) (i j : Fin n) :
    coordinateHessian (mollify k u) x i j = mollify k (fun y => coordinateHessian u y i j) x := by
  change coordinateDerivative (coordinateDerivative (mollify k u) j) i x = _
  rw [lipschitz_coordinateDerivative_mollify hLip,
    lipschitz_coordinateDerivative_mollify (lipschitz_coordinateDerivative_of_gradient_lipschitz hG j)]
  rfl

end KLS
end
