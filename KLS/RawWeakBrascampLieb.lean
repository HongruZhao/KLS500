import KLS.WeakBochner

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual inverse Hessian evaluated on an explicitly supplied raw
weak gradient. There is no assertion of classical differentiability. -/
def rawInverseHessianGradientForm (φ : Space n → ℝ) (F : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * F i x * F j x

theorem raw_inverse_hessian_gradient_young
    {φ : Space n → ℝ} {x : Space n} (hpos : (coordinateHessian φ x).PosDef)
    (F : Fin n → Space n → ℝ) (g : Space n → ℝ) :
    2 * (∑ i, F i x * coordinateDerivative g i x) ≤
      rawInverseHessianGradientForm φ F x + hessianGradientForm φ g x := by
  rw [rawInverseHessianGradientForm, hessianGradientForm,
    matrix_quadratic_sum_eq_dotProduct, matrix_quadratic_sum_eq_dotProduct]
  exact matrix_inverse_young hpos (fun i => F i x) (fun i => coordinateDerivative g i x)

/-- The genuine inverse-energy dual estimate holds for raw local weak
gradients and a C1,1 potential. All integrals are justified explicitly. -/
theorem brascampLieb_dual_diffusion_raw_weak
    {φ f g : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hG : LocallyLipschitz (gradient φ))
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hf : LocallyIntegrable f volume) (hFl : ∀ i, LocallyIntegrable (F i) volume)
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i)
    (hinv : Integrable (rawInverseHessianGradientForm φ F) (potentialMeasure φ))
    (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    2 * (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) -
      (∫ x, weightedDiffusion φ g x ^ 2 ∂potentialMeasure φ) ≤
        ∫ x, rawInverseHessianGradientForm φ F x ∂potentialMeasure φ := by
  have hp := raw_weak_gradient_pairing_eq_neg_diffusion hφ hf hFl hFw
    (hg.of_le (by norm_num)) hc
  have hboch := integral_weightedDiffusion_sq_C11 hφ hG hg hc
  have hsum : Integrable (fun x => ∑ i, F i x * coordinateDerivative g i x)
      (potentialMeasure φ) := integrable_finsetSum _ (fun i _ => hp.1 i)
  have hposμ : ∀ᵐ x ∂potentialMeasure φ, (coordinateHessian φ x).PosDef := (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le hpos
  have hright : Integrable (fun x => rawInverseHessianGradientForm φ F x + hessianGradientForm φ g x)
      (potentialMeasure φ) := hinv.add hboch.2.1
  have hy := integral_mono_ae (hsum.const_mul 2) hright
    (hposμ.mono fun x hx => raw_inverse_hessian_gradient_young hx F g)
  rw [integral_const_mul, integral_add hinv hboch.2.1] at hy
  have hpair : (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) =
      ∫ x, ∑ i, F i x * coordinateDerivative g i x ∂potentialMeasure φ := by
    rw [integral_finsetSum _ (fun i _ => hp.1 i), hp.2.2, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hpair]
  have hb := integral_hessianGradientForm_le_diffusion_sq_C11 hφ hG hg hc
  linarith

/-- Full finite-energy Brascamp--Lieb for an actual raw weak gradient.
The concrete diffusion-range density is the only closure premise. -/
theorem brascampLieb_variance_raw_weak_of_rangeDense
    {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LocallyLipschitz (gradient φ))
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hFl : ∀ i, LocallyIntegrable (F i) volume)
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i)
    (hinv : Integrable (rawInverseHessianGradientForm φ F) (potentialMeasure φ))
    (hdense : DiffusionRangeDense φ) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, rawInverseHessianGradientForm φ F x ∂potentialMeasure φ := by
  have hf := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure hf2 hφ.continuous
  let U : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  have hU : (U : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hclosure : CenteredL2.center (potentialMeasure φ) U ∈
      closure (compactDiffusionRange φ : Set (Lp ℝ 2 (potentialMeasure φ))) :=
    hdense _ (CenteredL2.integral_center _ U)
  have hbound : ∀ v ∈ compactDiffusionRange φ,
      2 * inner ℝ U v - ‖v‖ ^ 2 ≤
        ∫ x, rawInverseHessianGradientForm φ F x ∂potentialMeasure φ := by
    rintro v ⟨g, hg, hc, hv⟩
    have hi : inner ℝ U v =
        ∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hU, hv] with x hx hy
      simp [hx, hy, RCLike.inner_apply, mul_comm]
    have hn : ‖v‖ ^ 2 =
        ∫ x, weightedDiffusion φ g x ^ 2 ∂potentialMeasure φ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp [hx, pow_two]
    rw [hi, hn]
    exact brascampLieb_dual_diffusion_raw_weak hφ hG hpos hf hFl hFw hinv hg hc
  have he := CenteredL2.variance_le_of_center_mem_closure (potentialMeasure φ) hclosure hbound
  rwa [ProbabilityTheory.variance_congr hU] at he

end KLS
end
