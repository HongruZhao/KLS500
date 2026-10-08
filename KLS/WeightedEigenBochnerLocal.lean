import KLS.WeightedCompactSupport
import KLS.WeightedDiffusionLinear
import KLS.WeightedCaccioppoli

/-! Localized Bochner identity for actual classical weighted eigenfunctions. -/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators ContDiff

noncomputable section
set_option maxHeartbeats 800000
namespace KLS
variable {n : ℕ}

lemma continuous_hessianSquare {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (hessianSquare f) := by
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((contDiff_coordinateHessian hf (m := 0) (by norm_num) i j).continuous).pow 2

lemma continuous_hessianGradientForm {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f) :
    Continuous (hessianGradientForm φ f) := by
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous).mul
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous)).mul
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous)

/-- The exact cutoff error uses first derivatives of the cutoff only. -/
def bochnerCutoffError (ζ f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i

lemma continuous_bochnerCutoffError {ζ f : Space n → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hf : ContDiff ℝ 2 f) :
    Continuous (bochnerCutoffError ζ f) := by
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((contDiff_coordinateDerivative hζ (m := 0) (by norm_num) j).continuous).mul
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous)).mul
      ((contDiff_coordinateHessian hf (m := 0) (by norm_num) j i).continuous)

lemma hasCompactSupport_bochnerCutoffError {ζ f : Space n → ℝ}
    (hc : HasCompactSupport ζ) : HasCompactSupport (bochnerCutoffError ζ f) := by
  have h (i : Fin n) : HasCompactSupport (fun x => ∑ j : Fin n,
      coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i) := by
    convert
      (HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun j x => coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i)
        (fun j _ => (hasCompactSupport_coordinateDerivative hc j).mul_right.mul_right)) using 1
    funext x
    simp only [Finset.sum_apply]
  convert
    (HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i x => ∑ j : Fin n, coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i)
      (fun i _ => h i)) using 1
  funext x
  simp only [bochnerCutoffError, Finset.sum_apply]

/-- Localized Bochner identity, with all integration hypotheses supplied by the compact
multiplier. The eigenfunction itself has no support or growth hypothesis. -/
theorem integral_localized_bochner_gradient {φ f ζ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hζ : ContDiff ℝ 1 ζ)
    (hc : HasCompactSupport ζ) :
    (∫ x, ζ x * (hessianSquare f x + hessianGradientForm φ f x) ∂potentialMeasure φ) =
      -(∫ x, ζ x * inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) ∂potentialMeasure φ) -
        ∫ x, bochnerCutoffError ζ f x ∂potentialMeasure φ := by
  have hLd (i : Fin n) :=
    (contDiff_coordinateDerivative (contDiff_weightedDiffusion hφ hf) (m := 0) (by norm_num) i).continuous
  have hd (i : Fin n) : ContDiff ℝ 2 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (by norm_num) i
  have hdd (i j : Fin n) : Continuous (fun x => coordinateHessian f x j i) :=
    (contDiff_coordinateHessian hf (m := 0) (by norm_num) j i).continuous
  have hφdd (i j : Fin n) : Continuous (fun x => coordinateHessian φ x i j) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  have hζd (j : Fin n) :=
    (contDiff_coordinateDerivative hζ (m := 0) (by norm_num) j).continuous
  have hi (F : Space n → ℝ) (hF : Continuous F) :
      Integrable (fun x => ζ x * F x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hζ.continuous.mul hF) hc.mul_right
  have hcross (i j : Fin n) : Integrable
      (fun x => coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((hζd j).mul (hd i).continuous).mul (hdd i j))
      (hasCompactSupport_coordinateDerivative hc j).mul_right.mul_right
  have hcomm (i : Fin n) (x : Space n) :
      weightedDiffusion φ (coordinateDerivative f i) x =
        coordinateDerivative (weightedDiffusion φ f) i x +
          ∑ j, coordinateHessian φ x i j * coordinateDerivative f j x := by
    linarith [coordinateDerivative_weightedDiffusion hφ hf i x]
  have hrow (i : Fin n) :
      (∫ x, ζ x * (∑ j, coordinateHessian f x j i ^ 2 +
        ∑ j, coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x)
        ∂potentialMeasure φ) =
      -(∫ x, ζ x * (coordinateDerivative (weightedDiffusion φ f) i x * coordinateDerivative f i x) ∂potentialMeasure φ) -
        ∫ x, ∑ j, coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i
          ∂potentialMeasure φ := by
    let F : Space n → ℝ := fun x => ζ x * coordinateDerivative f i x
    have hF : ContDiff ℝ 1 F := hζ.mul ((hd i).of_le (by norm_num))
    have hdom := diffusionIntegrability_of_hasCompactSupport_left
      (hφ.of_le (by norm_num)) hF (hd i) hc.mul_right
    have hibp := integral_mul_weightedDiffusion (hφ.differentiable (by norm_num))
      (hF.differentiable (by norm_num))
      (fun j => (contDiff_coordinateDerivative (hd i) (m := 1) (by norm_num) j).differentiable
        (by norm_num)) hdom
    have hleft : (fun x => F x * weightedDiffusion φ (coordinateDerivative f i) x) =
        fun x => ζ x * (coordinateDerivative (weightedDiffusion φ f) i x * coordinateDerivative f i x) +
          ζ x * ∑ j, coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x := by
      funext x
      rw [hcomm]
      dsimp [F]
      simp only [Finset.mul_sum, mul_add]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring
    have hright : (fun x => inner ℝ (gradient F x) (gradient (coordinateDerivative f i) x)) =
        fun x => ζ x * (∑ j, coordinateHessian f x j i ^ 2) +
          ∑ j, coordinateDerivative ζ j x * coordinateDerivative f i x * coordinateHessian f x j i := by
      funext x
      rw [← sum_coordinateDerivative_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [F]
      rw [coordinateDerivative_mul (hζ.differentiable (by norm_num) x)
        ((hd i).differentiable (by norm_num) x)]
      dsimp [coordinateHessian]
      ring
    have hs : Integrable (fun x => ζ x * (coordinateDerivative (weightedDiffusion φ f) i x * coordinateDerivative f i x)) (potentialMeasure φ) :=
      hi _ ((hLd i).mul (hd i).continuous)
    have hhs : Integrable (fun x => ζ x * ∑ j, coordinateHessian f x j i ^ 2)
        (potentialMeasure φ) := hi _ (continuous_finsetSum _ fun j _ => (hdd i j).pow 2)
    have hcurv : Integrable (fun x => ζ x * ∑ j,
        coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x)
        (potentialMeasure φ) := hi _ (continuous_finsetSum _ fun j _ =>
          ((hφdd i j).mul (hd i).continuous).mul (hd j).continuous)
    have hx := integrable_finsetSum Finset.univ (fun j _ => hcross i j)
    rw [hleft, hright, integral_add hs hcurv,
      integral_add hhs hx] at hibp
    have hsplit : (fun x => ζ x * ((∑ j, coordinateHessian f x j i ^ 2) +
        ∑ j, coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x)) =
        fun x => ζ x * (∑ j, coordinateHessian f x j i ^ 2) +
          ζ x * ∑ j, coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x := by
      funext x
      ring
    rw [hsplit, integral_add hhs hcurv]
    linarith
  have hrows := congrArg (fun a : Fin n → ℝ => ∑ i, a i) (funext hrow)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hrows
  have hrowInt (i : Fin n) : Integrable
      (fun x => ζ x * ((∑ j, coordinateHessian f x j i ^ 2) +
        ∑ j, coordinateHessian φ x i j * coordinateDerivative f i x * coordinateDerivative f j x))
      (potentialMeasure φ) := hi _ ((continuous_finsetSum _ fun j _ => (hdd i j).pow 2).add
        (continuous_finsetSum _ fun j _ => ((hφdd i j).mul (hd i).continuous).mul (hd j).continuous))
  rw [← integral_finsetSum Finset.univ (fun i _ => hrowInt i),
    ← integral_finsetSum Finset.univ (fun i _ => hi (fun x => coordinateDerivative (weightedDiffusion φ f) i x * coordinateDerivative f i x) ((hLd i).mul (hd i).continuous)),
    ← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hcross i j))] at hrows
  convert hrows using 1
  · congr 1
    funext x
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    congr 1
    congr 1
    exact Finset.sum_comm
  · congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← Finset.mul_sum]
    congr 1
    exact (sum_coordinateDerivative_mul (weightedDiffusion φ f) f x).symm


/-- Localized Bochner identity, with all integration hypotheses supplied by the compact
multiplier. The eigenfunction itself has no support or growth hypothesis. -/
theorem integral_localized_bochner_eigenfunction {φ f ζ : Space n → ℝ} {lam : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hζ : ContDiff ℝ 1 ζ)
    (hc : HasCompactSupport ζ) (heq : ∀ x, weightedDiffusion φ f x = -lam * f x) :
    (∫ x, ζ x * (hessianSquare f x + hessianGradientForm φ f x) ∂potentialMeasure φ) =
      lam * (∫ x, ζ x * ‖gradient f x‖ ^ 2 ∂potentialMeasure φ) -
        ∫ x, bochnerCutoffError ζ f x ∂potentialMeasure φ := by
  have hgrad (x : Space n) : gradient (weightedDiffusion φ f) x = (-lam) • gradient f x := by
    have hfun : weightedDiffusion φ f = (-lam) • f := by
      funext y
      simpa only [Pi.smul_apply, smul_eq_mul] using heq y
    ext i
    rw [← coordinateDerivative_eq_gradient, hfun,
      coordinateDerivative_smul (hf.differentiable (by norm_num) x)]
    simp only [PiLp.smul_apply, smul_eq_mul, coordinateDerivative_eq_gradient]
  have hb := integral_localized_bochner_gradient hφ hf hζ hc
  have he : (fun x => ζ x * inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x)) =
      fun x => (-lam) * (ζ x * ‖gradient f x‖ ^ 2) := by
    funext x
    rw [hgrad, inner_smul_left]
    simp only [conj_trivial, real_inner_self_eq_norm_sq]
    ring
  rw [he, integral_const_mul] at hb
  linarith

/-- Localized Bochner identity on the actual diffusion domain. Both cutoff errors contain
only first derivatives of the compact multiplier, so no growth control on the drift is needed. -/
theorem integral_localized_bochner_diffusion {φ f ζ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hζ : ContDiff ℝ 1 ζ)
    (hc : HasCompactSupport ζ) :
    (∫ x, ζ x * (hessianSquare f x + hessianGradientForm φ f x) ∂potentialMeasure φ) =
      (∫ x, ζ x * weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) +
      (∫ x, weightedDiffusion φ f x * inner ℝ (gradient ζ x) (gradient f x) ∂potentialMeasure φ) -
      ∫ x, bochnerCutoffError ζ f x ∂potentialMeasure φ := by
  have hL := contDiff_weightedDiffusion hφ hf
  have hg := continuous_gradient_of_contDiff (hf.of_le (by norm_num))
  have hLg := continuous_gradient_of_contDiff hL
  have hζg := continuous_gradient_of_contDiff hζ
  let F : Space n → ℝ := fun x => ζ x * weightedDiffusion φ f x
  have hF : ContDiff ℝ 1 F := hζ.mul hL
  have hdom := diffusionIntegrability_of_hasCompactSupport_left
    (hφ.of_le (by norm_num)) hF (hf.of_le (by norm_num)) hc.mul_right
  have hibp := integral_mul_weightedDiffusion (hφ.differentiable (by norm_num))
    (hF.differentiable (by norm_num))
    (fun i => (contDiff_coordinateDerivative hf (m := 1) (by norm_num) i).differentiable
      (by norm_num)) hdom
  have hleft : (fun x => F x * weightedDiffusion φ f x) =
      fun x => ζ x * weightedDiffusion φ f x ^ 2 := by
    funext x
    dsimp [F]
    ring
  have hright : (fun x => inner ℝ (gradient F x) (gradient f x)) =
      fun x => ζ x * inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) +
        weightedDiffusion φ f x * inner ℝ (gradient ζ x) (gradient f x) := by
    funext x
    dsimp [F]
    rw [gradient_mul_real (hζ.differentiable (by norm_num) x) (hL.differentiable (by norm_num) x)]
    simp only [inner_add_left, inner_smul_left, conj_trivial]
    ring
  have hi1 : Integrable (fun x => ζ x *
      inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x)) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hζ.continuous.mul (hLg.inner hg)) hc.mul_right
  have hi2 : Integrable (fun x => weightedDiffusion φ f x *
      inner ℝ (gradient ζ x) (gradient f x)) (potentialMeasure φ) := by
    have he : (fun x => weightedDiffusion φ f x * inner ℝ (gradient ζ x) (gradient f x)) =
        fun x => ∑ i, weightedDiffusion φ f x * coordinateDerivative ζ i x * coordinateDerivative f i x := by
      funext x
      rw [← sum_coordinateDerivative_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact integrable_finsetSum Finset.univ fun i _ =>
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
        ((hL.continuous.mul ((contDiff_coordinateDerivative hζ (m := 0) (by norm_num) i).continuous)).mul
          ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous))
        (hasCompactSupport_coordinateDerivative hc i).mul_left.mul_right
  rw [hleft, hright, integral_add hi1 hi2] at hibp
  have hb := integral_localized_bochner_gradient hφ hf hζ hc
  linarith

end KLS
end

#print axioms KLS.integral_localized_bochner_gradient
#print axioms KLS.integral_localized_bochner_eigenfunction
#print axioms KLS.integral_localized_bochner_diffusion
