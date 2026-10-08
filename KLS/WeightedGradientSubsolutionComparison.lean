import KLS.GradientSquareIntegrability

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Actual Bochner, derived Hessian integrability, and the proved subsolution
maximum principle compare the squared gradient with a genuine elliptic solution. -/
theorem gradient_norm_sq_le_of_resolvent_equations {φ f g v : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ 1 g) (hv : ContDiff ℝ 3 v)
    {t : ℝ} (ht : 0 < t) (heq : ∀ x, f x - t * weightedDiffusion φ f x = g x)
    (hev : ∀ x, v x - t * weightedDiffusion φ v x = ‖gradient g x‖ ^ 2)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ))
    (hIv : Integrable v (potentialMeasure φ))
    (hgv : Integrable (gradient v) (potentialMeasure φ)) :
    ∀ x, ‖gradient f x‖ ^ 2 ≤ v x := by
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by simp)
  have hF : ContDiff ℝ 3 (fun x => ‖gradient f x‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  have hG := integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  have hH := (integrable_bochner_terms_of_diffusion_domain hφ hf3 hcurv hL hG).1
  have hGG := integrable_gradient_gradient_norm_sq (hf.of_le (by simp)) hd hH
  let u : Space n → ℝ := (fun x => ‖gradient f x‖ ^ 2)+(-1 : ℝ) • v
  have hu : ContDiff ℝ 3 u := hF.add (hv.const_smul (-1 : ℝ))
  have hI : Integrable u (potentialMeasure φ) := hG.add (hIv.smul (-1 : ℝ))
  have hgradU : gradient u = gradient (fun x => ‖gradient f x‖ ^ 2)+(-1 : ℝ) • gradient v := by
    funext x
    dsimp only [u]
    rw [gradient_add_real (hF.differentiable (by norm_num) x)
      ((hv.differentiable (by norm_num) x).const_smul (-1 : ℝ)),
      gradient_smul_real (hv.differentiable (by norm_num) x)]
    rfl
  have hGI : Integrable (gradient u) (potentialMeasure φ) := by
    rw [hgradU]
    exact hGG.add (hgv.smul (-1 : ℝ))
  have hsub (x : Space n) : u x-t*weightedDiffusion φ u x ≤ 0 := by
    have hb := gradient_norm_sq_resolvent_subsolution hφ hf3 hg ht heq hcurv x
    have hLdiff : weightedDiffusion φ u x =
        weightedDiffusion φ (fun y => ‖gradient f y‖ ^ 2) x+(-1 : ℝ)*weightedDiffusion φ v x := by
      dsimp only [u]
      rw [weightedDiffusion_add (f := fun y => ‖gradient f y‖ ^ 2) (g := (-1 : ℝ) • v)
        (hF.of_le (by norm_num)) ((hv.const_smul (-1 : ℝ)).of_le (by norm_num)),
        weightedDiffusion_smul (hv.of_le (by norm_num))]
    rw [hLdiff]
    dsimp only [u,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    linarith [hev x]
  have hmax := nonpos_of_weighted_resolvent_subsolution hφ hu ht hsub hI hGI.norm
  intro x
  have hx := hmax x
  change ‖gradient f x‖ ^ 2+(-1 : ℝ)*v x ≤ 0 at hx
  linarith

end KLS
end
