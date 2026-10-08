import KLS.WeightedDiffusionFiniteSum

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The pointwise Bochner identity is derived for the literal gradient and
diffusion from their coordinate product rule and actual commutator. -/
theorem weightedDiffusion_gradient_norm_sq {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (x : Space n) :
    weightedDiffusion φ (fun y => ‖gradient f y‖ ^ 2) x =
      2*hessianSquare f x+2*hessianGradientForm φ f x+
        2*inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) := by
  have hd (i : Fin n) : ContDiff ℝ 2 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (by norm_num) i
  have hc (i : Fin n) : weightedDiffusion φ (coordinateDerivative f i) x =
      coordinateDerivative (weightedDiffusion φ f) i x+
        ∑ j, coordinateHessian φ x i j*coordinateDerivative f j x := by
    linarith [coordinateDerivative_weightedDiffusion hφ hf i x]
  have hp (i : Fin n) : coordinateDerivative f i x*
      weightedDiffusion φ (coordinateDerivative f i) x =
      coordinateDerivative (weightedDiffusion φ f) i x*coordinateDerivative f i x+
        ∑ j, coordinateHessian φ x i j*coordinateDerivative f i x*coordinateDerivative f j x := by
    rw [hc,mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hpair : (∑ i, coordinateDerivative f i x*weightedDiffusion φ (coordinateDerivative f i) x) =
      inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x)+hessianGradientForm φ f x := by
    simp_rw [hp]
    rw [Finset.sum_add_distrib,sum_coordinateDerivative_mul]
    rfl
  have hsq : (fun y => ‖gradient f y‖ ^ 2) = fun y => ∑ i, coordinateDerivative f i y ^ 2 := by
    funext y
    simp only [EuclideanSpace.real_norm_sq_eq,coordinateDerivative_eq_gradient]
  rw [hsq,weightedDiffusion_fintype_sum φ (fun i => (hd i).pow 2)]
  calc
    _ = ∑ i, (2*coordinateDerivative f i x*weightedDiffusion φ (coordinateDerivative f i) x+
        2*‖gradient (coordinateDerivative f i) x‖ ^ 2) :=
      Finset.sum_congr rfl fun i _ => weightedDiffusion_sq φ (hd i) x
    _ = 2*(∑ i, coordinateDerivative f i x*weightedDiffusion φ (coordinateDerivative f i) x)+
        2*(∑ i, ‖gradient (coordinateDerivative f i) x‖ ^ 2) := by
      simp only [mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
    _ = _ := by rw [hpair,sum_norm_gradient_coordinateDerivative_sq];ring

/-- Nonnegative curvature and the actual resolvent equation make the squared
gradient a literal subsolution with the squared forcing gradient as source. -/
theorem gradient_norm_sq_resolvent_subsolution {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 1 g)
    {t : ℝ} (ht : 0 < t) (heq : ∀ x, f x - t * weightedDiffusion φ f x = g x)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x) (x : Space n) :
    ‖gradient f x‖ ^ 2-t*weightedDiffusion φ (fun y => ‖gradient f y‖ ^ 2) x ≤
      ‖gradient g x‖ ^ 2 := by
  have hip : t*inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) =
      ‖gradient f x‖ ^ 2-inner ℝ (gradient g x) (gradient f x) := by
    rw [gradient_diffusion_pairing_of_resolvent_equation
      (hf.of_le (by norm_num)) hg ht heq,← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  have hC : 2*inner ℝ (gradient g x) (gradient f x) ≤
      ‖gradient g x‖ ^ 2+‖gradient f x‖ ^ 2 := by
    nlinarith [real_inner_le_norm (gradient g x) (gradient f x),
      sq_nonneg (‖gradient g x‖-‖gradient f x‖)]
  have hp := mul_nonneg ht.le (add_nonneg (hessianSquare_nonneg f x) (hcurv x))
  rw [weightedDiffusion_gradient_norm_sq hφ hf]
  nlinarith

end KLS
end
