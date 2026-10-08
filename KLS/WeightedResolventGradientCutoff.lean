import KLS.WeightedResolventGradientIdentity

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The localized Bochner identity bounds the genuine gradient-level defect
by a cutoff-gradient error. The monotone level derivative has a favorable sign. -/
theorem integral_gradientLevelDefect_cutoff_le {φ f g χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 1 g)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hχsq : ∀ x, χ x ^ 2 ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hcgrad : ∀ x, ‖gradient χ x‖ ≤ c)
    {t : ℝ} (ht : 0 < t) (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hH : Integrable (hessianSquare f) (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) (M : ℝ) :
    (∫ x, χ x ^ 2 * gradientLevelDefect f g M x ∂potentialMeasure φ) ≤
      t*c*(∫ x, hessianSquare f x+‖gradient f x‖ ^ 2 ∂potentialMeasure φ) := by
  let ψ := smoothUpperTest (fun x => ‖gradient f x‖ ^ 2) (M ^ 2)
  let ζ := fun x => χ x ^ 2 * ψ x
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hψ : ContDiff ℝ 1 ψ := smoothUpperTest_contDiff
    (contDiff_gradient_norm_sq hf (by norm_num)) (M ^ 2)
  have hζ : ContDiff ℝ 1 ζ := (hχ.pow 2).mul hψ
  have hcχ : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two,Pi.mul_def] using hc.mul_right (f' := χ)
  have hcζ : HasCompactSupport ζ := hcχ.mul_right
  have hid := integral_localized_bochner_gradient hφ hf hζ hcζ
  have hmain : 0 ≤ ∫ x, ζ x*(hessianSquare f x+hessianGradientForm φ f x)
      ∂potentialMeasure φ := integral_nonneg fun x =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (smoothUpperTest_nonneg _ _ _))
      (add_nonneg (hessianSquare_nonneg _ _) (hcurv x))
  have hE : Integrable (bochnerCutoffError ζ f) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (continuous_bochnerCutoffError hζ hf2) (hasCompactSupport_bochnerCutoffError hcζ)
  have hbound (x : Space n) :
      -(c*(hessianSquare f x+‖gradient f x‖ ^ 2)) ≤ bochnerCutoffError ζ f x := by
    apply le_trans (neg_le_neg ?_)
      (bochnerCutoffError_gradient_level_cutoff_lower hf2 hχ (M ^ 2) x)
    exact mul_le_mul (hcgrad x)
      (add_le_add (mul_le_of_le_one_left (hessianSquare_nonneg _ _) (hχsq x)) le_rfl)
      (add_nonneg (mul_nonneg (sq_nonneg _) (hessianSquare_nonneg _ _)) (sq_nonneg _)) hc0
  have hEi := integral_mono ((hH.add hG).const_mul (-c)) hE (fun x => by
    simpa only [Pi.add_apply,neg_mul] using hbound x)
  rw [integral_const_mul] at hEi
  simp only [Pi.add_apply] at hEi
  have hreplace : (∫ x, ζ x * inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x)
      ∂potentialMeasure φ) =
      t⁻¹ * ∫ x, χ x ^ 2 * gradientLevelDefect f g M x ∂potentialMeasure φ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [gradient_diffusion_pairing_of_resolvent_equation hf1 hg ht heq]
      dsimp only [ζ,ψ,gradientLevelDefect]
      ring
  rw [hreplace] at hid
  have hout : t⁻¹*(∫ x, χ x ^ 2 * gradientLevelDefect f g M x ∂potentialMeasure φ) ≤
      c*(∫ x, hessianSquare f x+‖gradient f x‖ ^ 2 ∂potentialMeasure φ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hout ht.le
  simpa only [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using hmul

end KLS
end
