import KLS.WeightedResolventGradientSubcommutation
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Hessian Cauchy--Schwarz for the literal squared gradient. -/
theorem gradient_gradient_norm_sq_bound {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Space n) :
    ‖gradient (fun y => ‖gradient f y‖ ^ 2) x‖ ^ 2 ≤
      4 * ‖gradient f x‖ ^ 2 * hessianSquare f x := by
  have hG : ‖gradient f x‖ ^ 2 = ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,coordinateDerivative_eq_gradient]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [← coordinateDerivative_eq_gradient,coordinateDerivative_gradient_norm_sq hf]
  calc
    _ = 4 * ∑ j : Fin n, (∑ i : Fin n,
        coordinateDerivative f i x * coordinateHessian f x j i)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 4 * ∑ j : Fin n, (∑ i : Fin n, coordinateDerivative f i x ^ 2) *
        (∑ i : Fin n, coordinateHessian f x j i ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq
        Finset.univ (fun i => coordinateDerivative f i x) (fun i => coordinateHessian f x j i)
    _ = _ := by rw [← Finset.mul_sum, ← hG]; simp only [hessianSquare,mul_assoc]

def regularizedGradientNorm (ε : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  Real.sqrt (ε ^ 2 + ‖gradient f x‖ ^ 2)

theorem regularizedGradientNorm_pos {ε : ℝ} (hε : 0 < ε)
    (f : Space n → ℝ) (x : Space n) : 0 < regularizedGradientNorm ε f x := by
  unfold regularizedGradientNorm
  positivity

theorem regularizedGradientNorm_sq (ε : ℝ) (f : Space n → ℝ) (x : Space n) :
    regularizedGradientNorm ε f x ^ 2 = ε ^ 2 + ‖gradient f x‖ ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem regularizedGradientNorm_contDiff {ε : ℝ} (hε : 0 < ε)
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedGradientNorm ε f) := by
  exact (contDiff_const.add (contDiff_gradient_norm_sq hf (by simp))).sqrt
    (fun x => by positivity)

theorem regularizedGradientNorm_gradient_identity {ε : ℝ} (hε : 0 < ε)
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space n) :
    (2 * regularizedGradientNorm ε f x) • gradient (regularizedGradientNorm ε f) x =
      gradient (fun y => ‖gradient f y‖ ^ 2) x := by
  have hr := regularizedGradientNorm_contDiff hε hf
  have hG : ContDiff ℝ 1 (fun y => ‖gradient f y‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  rw [← gradient_sq_real (hr.differentiable (by simp))]
  have heq : (fun y => regularizedGradientNorm ε f y ^ 2) =
      (fun _ : Space n => ε ^ 2) + (fun y => ‖gradient f y‖ ^ 2) :=
    funext (regularizedGradientNorm_sq ε f)
  rw [heq,gradient_add_real (differentiableAt_const _) (hG.differentiable one_ne_zero x)]
  simp [gradient]

theorem regularizedGradientNorm_gradient_sq_le {ε : ℝ} (hε : 0 < ε)
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space n) :
    ‖gradient (regularizedGradientNorm ε f) x‖ ^ 2 ≤ hessianSquare f x := by
  have hid := congrArg (fun v : Space n => ‖v‖ ^ 2)
    (regularizedGradientNorm_gradient_identity hε hf x)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num)
    (regularizedGradientNorm_pos hε f x)),mul_pow] at hid
  have hsq := regularizedGradientNorm_sq ε f x
  have hb := gradient_gradient_norm_sq_bound (hf.of_le (by simp)) x
  have hH := hessianSquare_nonneg f x
  have hpos := regularizedGradientNorm_pos hε f x
  have he := mul_nonneg (sq_nonneg ε) hH
  have heqH := congrArg (fun a : ℝ => a * hessianSquare f x) hsq
  have hb2 : 4 * regularizedGradientNorm ε f x ^ 2 *
      ‖gradient (regularizedGradientNorm ε f) x‖ ^ 2 ≤
      4 * regularizedGradientNorm ε f x ^ 2 * hessianSquare f x := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * regularizedGradientNorm ε f x ^ 2)).mp hb2


/-- Cauchy--Schwarz after adjoining the common regularization coordinate. -/
theorem regularizedGradientNorm_inner_bound (ε : ℝ)
    (f g : Space n → ℝ) (x : Space n) :
    ε ^ 2 + inner ℝ (gradient g x) (gradient f x) ≤
      regularizedGradientNorm ε f x * regularizedGradientNorm ε g x := by
  have hsf := regularizedGradientNorm_sq ε f x
  have hsg := regularizedGradientNorm_sq ε g x
  have hprod : (regularizedGradientNorm ε f x * regularizedGradientNorm ε g x)^2 =
      (ε^2+‖gradient f x‖^2)*(ε^2+‖gradient g x‖^2) := by
    rw [mul_pow,hsf,hsg]
  have hp : 0 ≤ regularizedGradientNorm ε f x * regularizedGradientNorm ε g x :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hnon : 0 ≤ ε^2+‖gradient g x‖*‖gradient f x‖ := by positivity
  have hcs := real_inner_le_norm (gradient g x) (gradient f x)
  have hscalar : ε^2+‖gradient g x‖*‖gradient f x‖ ≤
      regularizedGradientNorm ε f x * regularizedGradientNorm ε g x := by
    nlinarith [sq_nonneg (ε*(‖gradient f x‖-‖gradient g x‖))]
  linarith

/-- The regularized actual gradient is an elliptic Kato subsolution. -/
theorem regularizedGradientNorm_resolvent_subsolution {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ 1 g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x) (x : Space n) :
    regularizedGradientNorm ε f x-t*weightedDiffusion φ (regularizedGradientNorm ε f) x ≤
      regularizedGradientNorm ε g x := by
  have hr := regularizedGradientNorm_contDiff hε hf
  have hG : ContDiff ℝ 2 (fun y => ‖gradient f y‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  have hconst : weightedDiffusion φ (fun _ : Space n => ε^2) x=0 := by
    have hd (i : Fin n) : coordinateDerivative (fun _ : Space n => ε^2) i=0 := by
      funext y
      simp [coordinateDerivative]
    simp [weightedDiffusion_eq_sum, coordinateHessian, hd, coordinateDerivative]
  have heqR : (fun y => regularizedGradientNorm ε f y^2) =
      (fun _ : Space n => ε^2)+(fun y => ‖gradient f y‖^2) :=
    funext (regularizedGradientNorm_sq ε f)
  have hdiff := weightedDiffusion_sq φ (hr.of_le (by simp)) x
  rw [heqR,weightedDiffusion_add contDiff_const hG,hconst,zero_add,
    weightedDiffusion_gradient_norm_sq hφ (hf.of_le (by simp))] at hdiff
  have hip : t*inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) =
      ‖gradient f x‖ ^ 2-inner ℝ (gradient g x) (gradient f x) := by
    rw [gradient_diffusion_pairing_of_resolvent_equation
      (hf.of_le (by simp)) hg ht heq,← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  have hK := regularizedGradientNorm_gradient_sq_le hε hf x
  have hs := regularizedGradientNorm_sq ε f x
  have hc := hcurv x
  have hdiffT := congrArg (fun a : ℝ => t*a) hdiff
  have hKt := mul_le_mul_of_nonneg_left hK ht.le
  have hct := mul_nonneg ht.le hc
  have hsub : regularizedGradientNorm ε f x *
      (regularizedGradientNorm ε f x-t*weightedDiffusion φ (regularizedGradientNorm ε f) x) ≤
      ε^2+inner ℝ (gradient g x) (gradient f x) := by nlinarith
  have hb := hsub.trans (regularizedGradientNorm_inner_bound ε f g x)
  rw [mul_comm (regularizedGradientNorm ε f x) (regularizedGradientNorm ε g x)] at hb
  exact (mul_le_mul_iff_right₀ (regularizedGradientNorm_pos hε f x)).mp (by
    simpa only [mul_comm (regularizedGradientNorm ε g x) (regularizedGradientNorm ε f x)] using hb)

end KLS
end
