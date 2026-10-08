import KLS.WeakHessianTensorSymmetry
import KLS.GradientCompositionCalculus

open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma locallyLipschitz_exp_scaled_momentExponent
    {u V : Space n → ℝ} (hu : LocallyLipschitz u) (hV : ContDiff ℝ 1 V)
    (hG : LocallyLipschitz (gradient u)) (s : ℝ) :
    LocallyLipschitz (fun x => Real.exp (s * (-u x + V (gradient u x)))) := by
  have hp := hu.prodMk (hV.locallyLipschitz.comp hG)
  have hc : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.exp (s * (-p.1 + p.2))) :=
    (contDiff_const.mul (contDiff_fst.neg.add contDiff_snd)).exp
  exact hc.locallyLipschitz.comp hp

/-- The exponential scalar in the actual Monge–Ampère equation has an
ordinary chain rule at every point where the actual gradient differentiates. -/
theorem coordinateDerivative_exp_scaled_momentExponent
    {u V : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (hV : DifferentiableAt ℝ V (gradient u x))
    (hG : DifferentiableAt ℝ (gradient u) x) (s : ℝ) (i : Fin n) :
    coordinateDerivative (fun y => Real.exp (s * (-u y + V (gradient u y)))) i x =
      Real.exp (s * (-u x + V (gradient u x))) * s *
        (-coordinateDerivative u i x +
          ∑ a, coordinateDerivative V a (gradient u x) * coordinateHessian u x i a) := by
  have hv : DifferentiableAt ℝ (fun y => V (gradient u y)) x := hV.comp x hG
  have hsum : DifferentiableAt ℝ (fun y => -u y + V (gradient u y)) x := hu.neg.add hv
  have hd : DifferentiableAt ℝ (fun y => s * (-u y + V (gradient u y))) x := hsum.const_mul s
  have he : coordinateDerivative (fun y => V (gradient u y)) i x =
      ∑ a, coordinateDerivative V a (gradient u x) * coordinateHessian u x i a := by
    rw [coordinateDerivative_comp hV hG]
    have heq (a : Fin n) : (fun y => gradient u y a) = coordinateDerivative u a :=
      funext fun y => (coordinateDerivative_eq_gradient u a y).symm
    simp_rw [heq]
    rfl
  change fderiv ℝ (fun y => Real.exp (s * (-u y + V (gradient u y)))) x
    (EuclideanSpace.single i 1) = _
  rw [fderiv_exp hd, fderiv_const_mul hsum, fderiv_fun_add (show DifferentiableAt ℝ (fun y => -u y) x from hu.neg) hv, fderiv_fun_neg]
  simp only [smul_apply, add_apply,
    neg_apply, smul_eq_mul]
  change Real.exp (s * (-u x + V (gradient u x))) *
    (s * (-coordinateDerivative u i x + coordinateDerivative (fun y => V (gradient u y)) i x)) = _
  rw [he]
  ring

/-- Both the determinant exponential and its reciprocal have genuine raw
weak derivatives with the explicit chain formula, locally bounded on every
compact set. No Hessian derivative is supplied to this scalar step. -/
theorem weak_exp_scaled_momentExponent
    {u V : Space n → ℝ} {G : ℝ≥0}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 1 V) (hG : LipschitzWith G (gradient u))
    (s : ℝ) (i : Fin n) :
    HasLocalWeakCoordinateDerivative
      (fun x => Real.exp (s * (-u x + V (gradient u x))))
      (fun x => Real.exp (s * (-u x + V (gradient u x))) * s *
        (-coordinateDerivative u i x +
          ∑ a, coordinateDerivative V a (gradient u x) * coordinateHessian u x i a)) i ∧
    (∀ S : Set (Space n), IsCompact S →
      MemLp (fun x => Real.exp (s * (-u x + V (gradient u x)))) ∞ (volume.restrict S)) ∧
    ∀ S : Set (Space n), IsCompact S →
      MemLp (fun x => Real.exp (s * (-u x + V (gradient u x))) * s *
        (-coordinateDerivative u i x +
          ∑ a, coordinateDerivative V a (gradient u x) * coordinateHessian u x i a))
        ∞ (volume.restrict S) := by
  have hloc := locallyLipschitz_exp_scaled_momentExponent hu.locallyLipschitz hV hG.locallyLipschitz s
  have he : coordinateDerivative (fun x => Real.exp (s * (-u x + V (gradient u x)))) i =ᵐ[volume]
      (fun x => Real.exp (s * (-u x + V (gradient u x))) * s *
        (-coordinateDerivative u i x +
          ∑ a, coordinateDerivative V a (gradient u x) * coordinateHessian u x i a)) := by
    filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
    exact coordinateDerivative_exp_scaled_momentExponent
      (hu.differentiable (by norm_num) x) (hV.differentiable (by norm_num) _) hx s i
  refine ⟨(hasLocalWeakCoordinateDerivative_of_locallyLipschitz hloc i).congr_ae
    Filter.EventuallyEq.rfl he, fun S hS => memLp_top_restrict_compact_of_continuous hloc.continuous hS, ?_⟩
  intro S hS
  exact (memLp_congr_ae (ae_restrict_of_ae he)).mp
    (memLp_top_coordinateDerivative_of_locallyLipschitz hloc i hS)

end KLS
end
