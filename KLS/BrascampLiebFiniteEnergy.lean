import KLS.WeightedDiffusionRange

/-!
# Brascamp–Lieb for noncompact tests with integrable inverse-Hessian energy

Only the auxiliary diffusion test is compact. Its compact support supplies
all integration-by-parts terms for arbitrary C¹ f. Actual L² and energy
integrability, together with the separately named genuine range density,
then give the full variance bound for this test.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

theorem brascampLieb_dual_diffusion_of_integrable_energy {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 3 g)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hinv : Integrable (inverseHessianGradientForm φ f) (potentialMeasure φ))
    (hgc : HasCompactSupport g) :
    2 * (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) -
      (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
  have hid := diffusionIntegrability_of_hasCompactSupport (hφ.of_le (by norm_num)) hf
    (hg.of_le (by norm_num)) hgc
  have hbd := bochnerIntegrability_of_hasCompactSupport hφ hg hgc
  have hy := integral_mono (hid.integrable_inner_gradient.const_mul 2)
    (hinv.add hbd.integrable_hessianGradientForm) (fun x => inverse_hessian_gradient_young hpos f g x)
  simp only [Pi.add_apply] at hy
  rw [integral_const_mul, integral_add hinv hbd.integrable_hessianGradientForm] at hy
  have hb := integral_hessianGradientForm_le_diffusion_sq hφ hg hgc
  have hi : (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ := by
    calc
      _ = -(∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_mul_weightedDiffusion_of_hasCompactSupport
          (hφ.of_le (by norm_num)) hf (hg.of_le (by norm_num)) hgc]
        ring
  rw [hi]
  linarith

theorem brascampLieb_variance_of_integrable_energy {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hinv : Integrable (inverseHessianGradientForm φ f) (potentialMeasure φ))
    (hdense : DiffusionRangeDense φ) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hclosure : CenteredL2.center (potentialMeasure φ) F ∈
      closure (compactDiffusionRange φ : Set (Lp ℝ 2 (potentialMeasure φ))) :=
    hdense _ (CenteredL2.integral_center _ F)
  have hbound : ∀ v ∈ compactDiffusionRange φ,
      2 * inner ℝ F v - ‖v‖ ^ 2 ≤
        ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ := by
    rintro v ⟨g, hg, hgc, hv⟩
    have hi : inner ℝ F v =
        ∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, hv] with x hx hy
      simp [hx, hy, RCLike.inner_apply, mul_comm]
    have hn : ‖v‖ ^ 2 =
        ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp [hx, pow_two]
    rw [hi, hn]
    exact brascampLieb_dual_diffusion_of_integrable_energy hφ hf hg hpos hinv hgc
  have he := CenteredL2.variance_le_of_center_mem_closure (potentialMeasure φ) hclosure hbound
  rwa [ProbabilityTheory.variance_congr hF] at he

end KLS
end

#print axioms KLS.brascampLieb_dual_diffusion_of_integrable_energy
#print axioms KLS.brascampLieb_variance_of_integrable_energy
