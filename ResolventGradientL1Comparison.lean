import ResolventGradientKato

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma regularizedGradientNorm_ge {ε : ℝ} (_hε : 0 ≤ ε)
    (f : Space n → ℝ) (x : Space n) : ε ≤ regularizedGradientNorm ε f x := by
  have hs := regularizedGradientNorm_sq ε f x
  have hn : 0 ≤ regularizedGradientNorm ε f x := Real.sqrt_nonneg _
  nlinarith [sq_nonneg ‖gradient f x‖]

lemma regularizedGradientNorm_le {ε : ℝ} (hε : 0 ≤ ε)
    (f : Space n → ℝ) (x : Space n) :
    regularizedGradientNorm ε f x ≤ ε+‖gradient f x‖ := by
  have hs := regularizedGradientNorm_sq ε f x
  have hn : 0 ≤ regularizedGradientNorm ε f x := Real.sqrt_nonneg _
  have hN := norm_nonneg (gradient f x)
  nlinarith [mul_nonneg hε hN]

lemma regularizedGradientNorm_gradient_norm_bound {ε : ℝ} (hε : 0 < ε)
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space n) :
    ‖gradient (regularizedGradientNorm ε f) x‖ ≤
      (2*ε)⁻¹*‖gradient (fun y => ‖gradient f y‖^2) x‖ := by
  have hid := congrArg (fun v : Space n => ‖v‖)
    (regularizedGradientNorm_gradient_identity hε hf x)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num)
    (regularizedGradientNorm_pos hε f x))] at hid
  have hge := regularizedGradientNorm_ge hε.le f x
  have hmul := mul_le_mul_of_nonneg_right hge
    (norm_nonneg (gradient (regularizedGradientNorm ε f) x))
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (by positivity : 0 < 2*ε)).mpr
  nlinarith

variable {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

lemma regularizedGradientNorm_memLp {ε : ℝ} (hε : 0 < ε)
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hgrad : MemLp (gradient f) 2 (potentialMeasure φ)) :
    MemLp (regularizedGradientNorm ε f) 2 (potentialMeasure φ) := by
  apply ((memLp_const ε).add hgrad.norm).mono'
    (regularizedGradientNorm_contDiff hε hf).continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (regularizedGradientNorm_pos hε f x)]
    exact regularizedGradientNorm_le hε.le f x

/-- The Kato subsolution is compared with a genuine scalar resolvent equation.
All global integrability needed by the maximum principle is derived. -/
theorem regularizedGradientNorm_le_of_resolvent_equations {f g v : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ 1 g) (hv : ContDiff ℝ 3 v)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hev : ∀ x, v x-t*weightedDiffusion φ v x=regularizedGradientNorm ε g x)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ))
    (hIv : Integrable v (potentialMeasure φ))
    (hgv : Integrable (gradient v) (potentialMeasure φ)) :
    ∀ x, regularizedGradientNorm ε f x ≤ v x := by
  have hr := regularizedGradientNorm_contDiff hε hf
  have hG := integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  have hH := (integrable_bochner_terms_of_diffusion_domain hφ
    (hf.of_le (by simp)) hcurv hL hG).1
  have hGG := integrable_gradient_gradient_norm_sq (hf.of_le (by simp)) hd hH
  have hIr := (regularizedGradientNorm_memLp hε hf
    (memLp_gradient_of_coordinateDerivative (hf.of_le (by simp)) hd)).integrable (by norm_num)
  have hGr : Integrable (gradient (regularizedGradientNorm ε f)) (potentialMeasure φ) := by
    apply (hGG.norm.const_mul ((2*ε)⁻¹)).mono'
      (continuous_gradient_of_contDiff (hr.of_le (by simp))).aestronglyMeasurable
    exact Eventually.of_forall (regularizedGradientNorm_gradient_norm_bound hε hf)
  let u : Space n → ℝ := regularizedGradientNorm ε f+(-1 : ℝ) • v
  have hu : ContDiff ℝ 3 u := (hr.of_le (by simp)).add (hv.const_smul (-1 : ℝ))
  have hI : Integrable u (potentialMeasure φ) := hIr.add (hIv.smul (-1 : ℝ))
  have hgradU : gradient u=gradient (regularizedGradientNorm ε f)+(-1 : ℝ) • gradient v := by
    funext x
    dsimp only [u]
    rw [gradient_add_real (hr.differentiable (by simp) x)
      ((hv.differentiable (by norm_num) x).const_smul (-1 : ℝ)),
      gradient_smul_real (hv.differentiable (by norm_num) x)]
    rfl
  have hGI : Integrable (gradient u) (potentialMeasure φ) := by
    rw [hgradU]
    exact hGr.add (hgv.smul (-1 : ℝ))
  have hsub (x : Space n) : u x-t*weightedDiffusion φ u x ≤ 0 := by
    have hb := regularizedGradientNorm_resolvent_subsolution hφ hf hg ht hε heq hcurv x
    have hLdiff : weightedDiffusion φ u x=
        weightedDiffusion φ (regularizedGradientNorm ε f) x+(-1 : ℝ)*weightedDiffusion φ v x := by
      dsimp only [u]
      rw [weightedDiffusion_add (f := regularizedGradientNorm ε f) (g := (-1 : ℝ) • v)
        (hr.of_le (by simp)) ((hv.const_smul (-1 : ℝ)).of_le (by norm_num)),
        weightedDiffusion_smul (hv.of_le (by norm_num))]
    rw [hLdiff]
    dsimp only [u,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    linarith [hev x]
  have hmax := nonpos_of_weighted_resolvent_subsolution hφ hu ht hsub hI hGI.norm
  intro x
  have hx := hmax x
  change regularizedGradientNorm ε f x+(-1 : ℝ)*v x ≤ 0 at hx
  linarith

end KLS
end
