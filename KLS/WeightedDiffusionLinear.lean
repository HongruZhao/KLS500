import KLS.BrascampLiebDuality

/-! # Actual linearity of weighted diffusion on smooth functions -/

open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma coordinateDerivative_add {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (f + g) i x = coordinateDerivative f i x + coordinateDerivative g i x := by
  unfold coordinateDerivative
  rw [fderiv_add hf hg]
  simp

lemma coordinateDerivative_smul {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    coordinateDerivative (c • f) i x = c * coordinateDerivative f i x := by
  unfold coordinateDerivative
  rw [fderiv_const_smul hf c]
  simp

lemma coordinateHessian_add {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) (i j : Fin n) :
    coordinateHessian (f + g) x i j = coordinateHessian f x i j + coordinateHessian g x i j := by
  have heq : coordinateDerivative (f + g) j = coordinateDerivative f j + coordinateDerivative g j := by
    funext y
    exact coordinateDerivative_add (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y) j
  change coordinateDerivative (coordinateDerivative (f + g) j) i x = _
  rw [heq, coordinateDerivative_add
    ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable (by norm_num) x)
    ((contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable (by norm_num) x)]
  rfl

lemma coordinateHessian_smul {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : Space n) (i j : Fin n) :
    coordinateHessian (c • f) x i j = c * coordinateHessian f x i j := by
  have heq : coordinateDerivative (c • f) j = c • coordinateDerivative f j := by
    funext y
    exact coordinateDerivative_smul (hf.differentiable (by norm_num) y) c j
  change coordinateDerivative (coordinateDerivative (c • f) j) i x = _
  rw [heq, coordinateDerivative_smul
    ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable (by norm_num) x)]
  rfl

lemma weightedDiffusion_zero (φ : Space n → ℝ) (x : Space n) :
    weightedDiffusion φ (0 : Space n → ℝ) x = 0 := by
  have hd (i : Fin n) : coordinateDerivative (0 : Space n → ℝ) i = 0 := by
    funext y
    simp [coordinateDerivative]
  simp [weightedDiffusion_eq_sum, coordinateHessian, hd, coordinateDerivative]

lemma weightedDiffusion_add {φ f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    weightedDiffusion φ (f + g) x = weightedDiffusion φ f x + weightedDiffusion φ g x := by
  simp_rw [weightedDiffusion_eq_sum, coordinateHessian_add hf hg,
    coordinateDerivative_add (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma weightedDiffusion_smul {φ f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : Space n) :
    weightedDiffusion φ (c • f) x = c * weightedDiffusion φ f x := by
  simp_rw [weightedDiffusion_eq_sum, coordinateHessian_smul hf,
    coordinateDerivative_smul (hf.differentiable (by norm_num) x)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end KLS
end

#print axioms KLS.weightedDiffusion_zero
#print axioms KLS.weightedDiffusion_add
#print axioms KLS.weightedDiffusion_smul
