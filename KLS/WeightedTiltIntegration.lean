import KLS.WeightedExponentialMoments
import KLS.WeightedGlobalIntegration
import KLS.TiltedMeasure

/-! BKL's tilted diffusion identity for the genuine normalized exponential tilt.
All exponential integrability and boundary passage are derived from the actual
lower Hessian and L² diffusion/gradient domain. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem gradient_exp_inner (z x : Space n) :
    gradient (fun y => Real.exp (inner ℝ z y)) x = Real.exp (inner ℝ z x) • z := by
  have hd := ((innerSL ℝ z).hasFDerivAt (x := x)).exp
  simp only [innerSL_apply_apply] at hd
  apply (toDual ℝ (Space n)).injective
  rw [toDual_gradient, hd.fderiv]
  ext y
  simp [toDual_apply_apply]

/-- Integrating the actual negative diffusion against the unnormalized tilt
equals the actual tilted directional gradient. -/
theorem integral_exp_inner_mul_neg_weightedDiffusion {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (z : Space n) :
    (∫ x, (-weightedDiffusion φ f x) * Real.exp (inner ℝ z x) ∂potentialMeasure φ) =
      ∫ x, inner ℝ z (gradient f x) * Real.exp (inner ℝ z x) ∂potentialMeasure φ := by
  have hq : ContDiff ℝ 1 (fun x : Space n => Real.exp (inner ℝ z x)) := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ z).contDiff.exp
  have hq2 := memLp_exp_inner_potentialMeasure hφ hκ hlower z
  have hQ : Integrable (fun x =>
      ‖gradient (fun y => Real.exp (inner ℝ z y)) x‖ ^ 2) (potentialMeasure φ) := by
    convert hq2.integrable_sq.const_mul (‖z‖ ^ 2) using 1
    funext x
    rw [gradient_exp_inner, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
    ring
  have hi := integral_mul_weightedDiffusion_of_L2_domain
    (hφ.of_le (by norm_num)) hf hq hL hq2 hF hQ
  have hgrad : (fun x : Space n =>
      inner ℝ (gradient (fun y => Real.exp (inner ℝ z y)) x) (gradient f x)) =
      fun x => inner ℝ z (gradient f x) * Real.exp (inner ℝ z x) := by
    funext x
    rw [gradient_exp_inner, inner_smul_left]
    simp only [conj_trivial]
    ring
  rw [hgrad] at hi
  calc
    _ = -(∫ x, Real.exp (inner ℝ z x) * weightedDiffusion φ f x ∂potentialMeasure φ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    _ = _ := by linarith

/-- The genuine exponential tilt is a probability without compact-support assumptions. -/
theorem exponentialTilt_potentialMeasure_isProbability {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (z : Space n) :
    IsProbabilityMeasure (exponentialTilt (potentialMeasure φ) z) :=
  isProbabilityMeasure_tilted (integrable_exp_inner_potentialMeasure hφ hκ hlower z)

/-- The actual normalized-tilt identity BKL (48), throughout the smooth L²
diffusion/gradient domain. No polynomial-growth or tilted identity premise is used. -/
theorem weightedDiffusion_tiltAverage {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) (z : Space n) :
    tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x)
      (fun x => -weightedDiffusion φ f x) =
    tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x)
      (fun x => inner ℝ z (gradient f x)) := by
  rw [tiltAverage_eq_ratio, tiltAverage_eq_ratio,
    integral_exp_inner_mul_neg_weightedDiffusion hφ hκ hlower hf hL hF]

/-- The actual vector gradient is integrable under every normalized tilt. -/
theorem integrable_gradient_exponentialTilt_of_L2 {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 1 f)
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) (z : Space n) :
    Integrable (gradient f) (exponentialTilt (potentialMeasure φ) z) := by
  have hfn : MemLp (fun x => ‖gradient f x‖) 2 (potentialMeasure φ) :=
    (memLp_two_iff_integrable_sq
      (continuous_gradient_of_contDiff hf).norm.aestronglyMeasurable).mpr hF
  have hq2 := memLp_exp_inner_potentialMeasure hφ hκ hlower z
  have hqe : ContDiff ℝ 1 (fun x : Space n => Real.exp (inner ℝ z x)) := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ z).contDiff.exp
  have he : Continuous (fun x : Space n => Real.exp (inner ℝ z x)) := hqe.continuous
  change Integrable (gradient f) ((potentialMeasure φ).tilted (fun x => inner ℝ z x))
  rw [integrable_tilted_iff (integrable_exp_inner_potentialMeasure hφ hκ hlower z)]
  apply (integrable_norm_iff (he.smul (continuous_gradient_of_contDiff hf)).aestronglyMeasurable).mp
  convert hq2.integrable_mul hfn using 1
  funext x
  change ‖Real.exp (inner ℝ z x) • gradient f x‖ = Real.exp (inner ℝ z x) * ‖gradient f x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Literal vector form of BKL (48): `F_{-L f}(z) = ⟨z,F_{∇ f}(z)⟩`. -/
theorem weightedDiffusion_exponentialTilt_identity {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) (z : Space n) :
    (∫ x, -weightedDiffusion φ f x ∂exponentialTilt (potentialMeasure φ) z) =
      inner ℝ z (∫ x, gradient f x ∂exponentialTilt (potentialMeasure φ) z) := by
  change tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x)
    (fun x => -weightedDiffusion φ f x) = _
  rw [weightedDiffusion_tiltAverage hφ hκ hlower hf hL hF]
  simpa only [tiltAverage, exponentialTilt, innerSL_apply_apply] using
    (innerSL ℝ z).integral_comp_comm
      (integrable_gradient_exponentialTilt_of_L2 hφ hκ hlower (hf.of_le (by norm_num)) hF z)

end KLS
end

#print axioms KLS.gradient_exp_inner
#print axioms KLS.integral_exp_inner_mul_neg_weightedDiffusion
#print axioms KLS.exponentialTilt_potentialMeasure_isProbability
#print axioms KLS.weightedDiffusion_tiltAverage
#print axioms KLS.integrable_gradient_exponentialTilt_of_L2
#print axioms KLS.weightedDiffusion_exponentialTilt_identity
