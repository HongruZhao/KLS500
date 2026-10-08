import KLS.HessianMetricComposition
import KLS.WeightedDiffusionLinear

/-! # Actual linearity and product calculus of the Hessian diffusion -/

open InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma coordinateHessian_sum {ι : Type*} [Fintype ι] {f : ι → Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 2 (f k)) (x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => ∑ k, f k y) x i j = ∑ k, coordinateHessian (f k) x i j := by
  have heq : coordinateDerivative (fun y => ∑ k, f k y) j =
      fun y => ∑ k, coordinateDerivative (f k) j y := by
    funext y
    exact coordinateDerivative_sum (fun k => (hf k).differentiable (by norm_num) y) j
  change coordinateDerivative (coordinateDerivative (fun y => ∑ k, f k y) j) i x = _
  rw [heq]
  exact coordinateDerivative_sum (fun k =>
    (contDiff_coordinateDerivative (hf k) (m := 1) (by norm_num) j).differentiable (by norm_num) x) i

lemma coordinateHessian_mul {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => f y * g y) x i j =
      coordinateHessian f x i j * g x + coordinateDerivative f j x * coordinateDerivative g i x +
        (coordinateDerivative f i x * coordinateDerivative g j x + f x * coordinateHessian g x i j) := by
  have hf' : Differentiable ℝ (coordinateDerivative f j) :=
    (contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable (by norm_num)
  have hg' : Differentiable ℝ (coordinateDerivative g j) :=
    (contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable (by norm_num)
  have heq : coordinateDerivative (fun y => f y * g y) j =
      fun y => coordinateDerivative f j y * g y + f y * coordinateDerivative g j y := by
    funext y
    exact coordinateDerivative_mul (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y) j
  change coordinateDerivative (coordinateDerivative (fun y => f y * g y) j) i x = _
  rw [heq]
  change coordinateDerivative ((fun y => coordinateDerivative f j y * g y) +
    (fun y => f y * coordinateDerivative g j y)) i x = _
  rw [coordinateDerivative_add (f := fun y => coordinateDerivative f j y * g y)
    (g := fun y => f y * coordinateDerivative g j y) ((hf' x).mul (hg.differentiable (by norm_num) x))
    ((hf.differentiable (by norm_num) x).mul (hg' x)),
    coordinateDerivative_mul (hf' x) (hg.differentiable (by norm_num) x),
    coordinateDerivative_mul (hf.differentiable (by norm_num) x) (hg' x)]
  rfl

lemma hessianMetricDiffusion_sum (φ V : Space n → ℝ)
    {ι : Type*} [Fintype ι] {f : ι → Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 2 (f k)) (x : Space n) :
    hessianMetricDiffusion φ V (fun y => ∑ k, f k y) x =
      ∑ k, hessianMetricDiffusion φ V (f k) x := by
  unfold hessianMetricDiffusion
  simp_rw [coordinateHessian_sum hf, coordinateDerivative_sum
    (fun k => (hf k).differentiable (by norm_num) x), Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = ∑ i, ∑ k, ∑ j, (coordinateHessian φ x)⁻¹ i j * coordinateHessian (f k) x i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · exact Finset.sum_comm

lemma hessianMetricDiffusion_smul (φ V : Space n → ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (c : ℝ) (x : Space n) :
    hessianMetricDiffusion φ V (c • f) x = c * hessianMetricDiffusion φ V f x := by
  unfold hessianMetricDiffusion
  simp_rw [coordinateHessian_smul hf, coordinateDerivative_smul
    (hf.differentiable (by norm_num) x), mul_left_comm _ c,
    ← Finset.mul_sum, ← mul_sub]

def hessianMetricGradientPair (φ f g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * coordinateDerivative f i x * coordinateDerivative g j x

lemma hessianMetricGradientPair_comm {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (f g : Space n → ℝ) (x : Space n) :
    hessianMetricGradientPair φ f g x = hessianMetricGradientPair φ g f x := by
  unfold hessianMetricGradientPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [((coordinateHessian_symmetric hφ x).inv).apply i j]
  ring

/-- The actual product rule uses symmetry of the genuine inverse Hessian. -/
theorem hessianMetricDiffusion_mul {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (V : Space n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    hessianMetricDiffusion φ V (fun y => f y * g y) x =
      f x * hessianMetricDiffusion φ V g x + g x * hessianMetricDiffusion φ V f x +
        2 * hessianMetricGradientPair φ f g x := by
  have hmix : (∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      (coordinateDerivative f j x * coordinateDerivative g i x)) = hessianMetricGradientPair φ f g x := by
    rw [hessianMetricGradientPair_comm hφ]
    unfold hessianMetricGradientPair
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold hessianMetricDiffusion
  simp_rw [coordinateHessian_mul hf hg, coordinateDerivative_mul
    (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x),
    mul_add, Finset.sum_add_distrib]
  rw [hmix]
  have hF : (∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * (coordinateHessian f x i j * g x)) =
      g x * ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * coordinateHessian f x i j := by
    simp_rw [Finset.mul_sum]
    congr 1
    funext i
    congr 1
    funext j
    ring
  have hG : (∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * (f x * coordinateHessian g x i j)) =
      f x * ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * coordinateHessian g x i j := by
    simp_rw [Finset.mul_sum, mul_left_comm _ (f x)]
  have hFG : (∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      (coordinateDerivative f i x * coordinateDerivative g j x)) = hessianMetricGradientPair φ f g x := by
    simp only [hessianMetricGradientPair, mul_assoc]
  have hdF : (∑ i, coordinateDerivative V i (gradient φ x) * (coordinateDerivative f i x * g x)) =
      g x * ∑ i, coordinateDerivative V i (gradient φ x) * coordinateDerivative f i x := by
    simp_rw [Finset.mul_sum]
    congr 1
    funext i
    ring
  have hdG : (∑ i, coordinateDerivative V i (gradient φ x) * (f x * coordinateDerivative g i x)) =
      f x * ∑ i, coordinateDerivative V i (gradient φ x) * coordinateDerivative g i x := by
    simp_rw [Finset.mul_sum, mul_left_comm _ (f x)]
  rw [hF, hG, hFG, hdF, hdG]
  ring

end KLS
end

#print axioms KLS.coordinateHessian_mul
#print axioms KLS.hessianMetricDiffusion_sum
#print axioms KLS.hessianMetricDiffusion_mul
