import KLS.WeightedEigenBochnerLocal
import KLS.WeightedFaithfulCutoff
import KLS.ConvexHessian

/-! Pointwise and integrated bounds for the actual compact-cutoff Bochner errors. -/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators ContDiff

noncomputable section
set_option maxHeartbeats 800000
namespace KLS
variable {n : ℕ}

lemma bochnerCutoffError_sq {χ f : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    bochnerCutoffError (fun y => χ y ^ 2) f x =
      ∑ i : Fin n, 2 * χ x * coordinateDerivative f i x *
        inner ℝ (gradient χ x) (gradient (coordinateDerivative f i) x) := by
  unfold bochnerCutoffError
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_coordinateDerivative_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun y => χ y ^ 2) = fun y => χ y * χ y := by funext y; ring
  rw [he, coordinateDerivative_mul (hχ x) (hχ x)]
  dsimp [coordinateHessian]
  ring

lemma abs_cutoff_inner_young (a b : ℝ) (v w : Space n) :
    |2 * a * b * inner ℝ v w| ≤ a ^ 2 / 2 * ‖w‖ ^ 2 + 2 * b ^ 2 * ‖v‖ ^ 2 := by
  have hp := real_inner_self_nonneg (x := a • w + (2 * b) • v)
  have hm := real_inner_self_nonneg (x := a • w - (2 * b) • v)
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq,
    real_inner_comm w v] at hp hm
  rw [real_inner_comm v w] at hp hm
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The cutoff Hessian error absorbs half the localized Hessian energy. -/
theorem abs_bochnerCutoffError_sq_le {χ f : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    |bochnerCutoffError (fun y => χ y ^ 2) f x| ≤
      χ x ^ 2 / 2 * hessianSquare f x +
        2 * ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2 := by
  rw [bochnerCutoffError_sq hχ]
  calc
    _ ≤ ∑ i : Fin n, |2 * χ x * coordinateDerivative f i x *
        inner ℝ (gradient χ x) (gradient (coordinateDerivative f i) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, (χ x ^ 2 / 2 * ‖gradient (coordinateDerivative f i) x‖ ^ 2 +
        2 * coordinateDerivative f i x ^ 2 * ‖gradient χ x‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => abs_cutoff_inner_young _ _ _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_norm_gradient_coordinateDerivative_sq]
      congr 1
      simp_rw [mul_assoc, mul_comm (coordinateDerivative f _ x ^ 2) (‖gradient χ x‖ ^ 2), ← mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      simp only [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]

lemma abs_cutoff_inner_vanishing (a b : ℝ) (v w : Space n) :
    |2 * a * b * inner ℝ v w| ≤ ‖v‖ * (a ^ 2 * ‖w‖ ^ 2 + b ^ 2) := by
  have hi := abs_real_inner_le_norm v w
  have hab : 0 ≤ 2 * |a| * |b| := by positivity
  calc
    _ = (2 * |a| * |b|) * |inner ℝ v w| := by rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ (2 * |a| * |b|) * (‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left hi hab
    _ ≤ _ := by
      have hs : 2 * |a| * |b| * ‖w‖ ≤ |a| ^ 2 * ‖w‖ ^ 2 + |b| ^ 2 := by
        nlinarith [sq_nonneg (|a| * ‖w‖ - |b|)]
      have hm := mul_le_mul_of_nonneg_left hs (norm_nonneg v)
      simp only [sq_abs] at hm
      nlinarith only [hm]

/-- Once the Hessian is square integrable, the cutoff error has a vanishing L¹ majorant. -/
theorem abs_bochnerCutoffError_sq_le_vanishing {χ f : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    |bochnerCutoffError (fun y => χ y ^ 2) f x| ≤
      ‖gradient χ x‖ * (χ x ^ 2 * hessianSquare f x + ‖gradient f x‖ ^ 2) := by
  rw [bochnerCutoffError_sq hχ]
  calc
    _ ≤ ∑ i : Fin n, |2 * χ x * coordinateDerivative f i x *
        inner ℝ (gradient χ x) (gradient (coordinateDerivative f i) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ‖gradient χ x‖ *
        (χ x ^ 2 * ‖gradient (coordinateDerivative f i) x‖ ^ 2 + coordinateDerivative f i x ^ 2) :=
      Finset.sum_le_sum fun i _ => abs_cutoff_inner_vanishing _ _ _ _
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_norm_gradient_coordinateDerivative_sq]
      congr 2
      simp only [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]

lemma cutoff_diffusion_error_sq {φ f χ : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    weightedDiffusion φ f x * inner ℝ (gradient (fun y => χ y ^ 2) x) (gradient f x) =
      2 * χ x * weightedDiffusion φ f x * inner ℝ (gradient χ x) (gradient f x) := by
  have he : (fun y => χ y ^ 2) = fun y => χ y * χ y := by funext y; ring
  rw [he, gradient_mul_real (hχ x) (hχ x)]
  simp only [inner_add_left, inner_smul_left, conj_trivial]
  ring

lemma abs_cutoff_diffusion_error_le {φ f χ : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    |weightedDiffusion φ f x * inner ℝ (gradient (fun y => χ y ^ 2) x) (gradient f x)| ≤
      χ x ^ 2 * weightedDiffusion φ f x ^ 2 + ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2 := by
  rw [cutoff_diffusion_error_sq hχ]
  have hi := abs_real_inner_le_norm (gradient χ x) (gradient f x)
  have hnon : 0 ≤ 2 * |χ x| * |weightedDiffusion φ f x| := by positivity
  calc
    _ = (2 * |χ x| * |weightedDiffusion φ f x|) * |inner ℝ (gradient χ x) (gradient f x)| := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    _ ≤ (2 * |χ x| * |weightedDiffusion φ f x|) * (‖gradient χ x‖ * ‖gradient f x‖) :=
      mul_le_mul_of_nonneg_left hi hnon
    _ ≤ _ := by
      nlinarith [sq_nonneg (|χ x| * |weightedDiffusion φ f x| - ‖gradient χ x‖ * ‖gradient f x‖),
        sq_abs (χ x), sq_abs (weightedDiffusion φ f x)]

lemma abs_cutoff_diffusion_error_le_vanishing {φ f χ : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (x : Space n) :
    |weightedDiffusion φ f x * inner ℝ (gradient (fun y => χ y ^ 2) x) (gradient f x)| ≤
      ‖gradient χ x‖ * (χ x ^ 2 * ‖gradient f x‖ ^ 2 + weightedDiffusion φ f x ^ 2) := by
  rw [cutoff_diffusion_error_sq hχ]
  exact abs_cutoff_inner_vanishing _ _ _ _

/-- A uniform localized estimate follows from the actual L² diffusion and gradient.
The curvature hypothesis is a pointwise nonnegativity condition, not an integration premise. -/
theorem integral_cutoff_bochnerDensity_le {φ f χ : Space n → ℝ} {K : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hK : 0 ≤ K) (hgradχ : ∀ x, ‖gradient χ x‖ ≤ K)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    (∫ x, χ x ^ 2 * (hessianSquare f x + hessianGradientForm φ f x) ∂potentialMeasure φ) ≤
      4 * (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) +
        6 * K ^ 2 * (∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ) := by
  let S : Space n → ℝ := fun x => hessianSquare f x + hessianGradientForm φ f x
  let D : Space n → ℝ := fun x => weightedDiffusion φ f x *
    inner ℝ (gradient (fun y => χ y ^ 2) x) (gradient f x)
  let B : Space n → ℝ := bochnerCutoffError (fun y => χ y ^ 2) f
  have hχsq (x : Space n) : χ x ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
  have hgχsq (x : Space n) : ‖gradient χ x‖ ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hgradχ x) 2
  have hS0 (x : Space n) : 0 ≤ S x := add_nonneg (hessianSquare_nonneg _ _) (hcurv x)
  have hSc : Continuous S :=
    (continuous_hessianSquare (hf.of_le (by norm_num))).add
      (continuous_hessianGradientForm hφ (hf.of_le (by norm_num)))
  have hχc : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ)
  have hIS : Integrable (fun x => χ x ^ 2 * S x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hχ.continuous.pow 2).mul hSc) hχc.mul_right
  have hIL : Integrable (fun x => χ x ^ 2 * weightedDiffusion φ f x ^ 2) (potentialMeasure φ) :=
    hL.integrable_sq.mono' ((hχ.continuous.pow 2).aestronglyMeasurable.mul (hL.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact mul_le_of_le_one_left (sq_nonneg _) (hχsq x))
  have hBD (x : Space n) : |D x| ≤ χ x ^ 2 * weightedDiffusion φ f x ^ 2 +
      K ^ 2 * ‖gradient f x‖ ^ 2 :=
    (abs_cutoff_diffusion_error_le (hχ.differentiable (by norm_num)) x).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hgχsq x) (sq_nonneg _)))
  have hID : Integrable D (potentialMeasure φ) :=
    (hIL.add (hG.const_mul (K ^ 2))).mono'
      ((contDiff_weightedDiffusion hφ hf).continuous.aestronglyMeasurable.mul
        ((continuous_gradient_of_contDiff (hχ.pow 2)).inner
          (continuous_gradient_of_contDiff (hf.of_le (by norm_num)))).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hBD x)
  have hIB : Integrable B (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (continuous_bochnerCutoffError (hχ.pow 2) (hf.of_le (by norm_num)))
      (hasCompactSupport_bochnerCutoffError hχc)
  have hBB (x : Space n) : -B x ≤ (χ x ^ 2 * S x) / 2 +
      2 * K ^ 2 * ‖gradient f x‖ ^ 2 := by
    have hb := abs_bochnerCutoffError_sq_le (hχ.differentiable (by norm_num)) (f := f) x
    have hmul := mul_nonneg (sq_nonneg (χ x)) (hcurv x)
    have hb2 := mul_le_mul_of_nonneg_right (hgχsq x) (sq_nonneg (‖gradient f x‖))
    have hneg := neg_le_abs (B x)
    dsimp [B, S] at *
    nlinarith
  have hDint := integral_mono hID (hIL.add (hG.const_mul (K ^ 2)))
    (fun x => (le_abs_self (D x)).trans (hBD x))
  have hBint := integral_mono hIB.neg ((hIS.div_const 2).add (hG.const_mul (2 * K ^ 2))) hBB
  simp only [Pi.neg_apply, Pi.add_apply] at hBint hDint
  rw [integral_neg, integral_add (hIS.div_const 2) (hG.const_mul (2 * K ^ 2)),
    integral_div, integral_const_mul] at hBint
  rw [integral_add hIL (hG.const_mul (K ^ 2)), integral_const_mul] at hDint
  have hLint := integral_mono hIL hL.integrable_sq fun x =>
    mul_le_of_le_one_left (sq_nonneg _) (hχsq x)
  have he := integral_localized_bochner_diffusion hφ hf (hχ.pow 2) hχc
  change (∫ x, χ x ^ 2 * S x ∂potentialMeasure φ) =
    (∫ x, χ x ^ 2 * weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) +
    (∫ x, D x ∂potentialMeasure φ) - (∫ x, B x ∂potentialMeasure φ) at he
  change (∫ x, χ x ^ 2 * S x ∂potentialMeasure φ) ≤ _
  linarith

end KLS
end

#print axioms KLS.abs_bochnerCutoffError_sq_le
#print axioms KLS.abs_bochnerCutoffError_sq_le_vanishing
#print axioms KLS.abs_cutoff_diffusion_error_le
#print axioms KLS.integral_cutoff_bochnerDensity_le
