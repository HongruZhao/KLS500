import KLS.ActualGradientIntegrability

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Three literal resolvent equations imply the pointwise variance estimate.
The comparison function's value and gradient integrability are derived from
its actual constituents, and the global subsolution principle is proved. -/
theorem resolvent_variance_of_equations {φ f g v w : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f)
    (hv : ContDiff ℝ 3 v) (hw : ContDiff ℝ 3 w)
    {t : ℝ} (ht : 0 < t)
    (heq : ∀ x, f x - t * weightedDiffusion φ f x = g x)
    (hev : ∀ x, v x - t * weightedDiffusion φ v x = ‖gradient f x‖ ^ 2)
    (hew : ∀ x, w x - t * weightedDiffusion φ w x = g x ^ 2)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hgradf : MemLp (gradient f) 2 (potentialMeasure φ))
    (hIv : Integrable v (potentialMeasure φ)) (hIw : Integrable w (potentialMeasure φ))
    (hgv : Integrable (gradient v) (potentialMeasure φ))
    (hgw : Integrable (gradient w) (potentialMeasure φ)) :
    ∀ x, f x ^ 2+2*t*v x ≤ w x := by
  let u : Space n → ℝ := (fun x => f x ^ 2)+(2*t) • v+(-1 : ℝ) • w
  have hu : ContDiff ℝ 3 u := ((hf.pow 2).add (hv.const_smul (2*t))).add (hw.const_smul (-1 : ℝ))
  have hI : Integrable u (potentialMeasure φ) :=
    ((hf2.integrable_sq).add (hIv.smul (2*t))).add (hIw.smul (-1 : ℝ))
  have hgradU : gradient u =
      (gradient (fun x => f x ^ 2)+(2*t) • gradient v)+(-1 : ℝ) • gradient w := by
    funext x
    dsimp only [u]
    rw [gradient_add_real (((hf.pow 2).differentiable (by norm_num) x).add
      ((hv.differentiable (by norm_num) x).const_smul (2*t)))
      ((hw.differentiable (by norm_num) x).const_smul (-1 : ℝ)),
      gradient_add_real ((hf.pow 2).differentiable (by norm_num) x)
        ((hv.differentiable (by norm_num) x).const_smul (2*t)),
      gradient_smul_real (hv.differentiable (by norm_num) x),
      gradient_smul_real (hw.differentiable (by norm_num) x)]
    rfl
  have hGI : Integrable (gradient u) (potentialMeasure φ) := by
    rw [hgradU]
    exact ((integrable_gradient_sq_of_memLp (hf.of_le (by norm_num)) hf2 hgradf).add
      (hgv.smul (2*t))).add (hgw.smul (-1 : ℝ))
  have hsub (x : Space n) : u x-t*weightedDiffusion φ u x ≤ 0 := by
    have hL : weightedDiffusion φ u x =
        weightedDiffusion φ (fun y => f y ^ 2) x+
          (2*t)*weightedDiffusion φ v x+(-1 : ℝ)*weightedDiffusion φ w x := by
      dsimp only [u]
      rw [weightedDiffusion_add (f := (fun y => f y ^ 2)+(2*t) • v)
        (g := (-1 : ℝ) • w)
        (((hf.pow 2).add (hv.const_smul (2*t))).of_le (by norm_num))
        ((hw.const_smul (-1 : ℝ)).of_le (by norm_num)),
        weightedDiffusion_add (f := fun y => f y ^ 2) (g := (2*t) • v)
          ((hf.pow 2).of_le (by norm_num))
          ((hv.const_smul (2*t)).of_le (by norm_num)),
        weightedDiffusion_smul (hv.of_le (by norm_num)),
        weightedDiffusion_smul (hw.of_le (by norm_num))]
    rw [hL,weightedDiffusion_sq φ (hf.of_le (by norm_num))]
    have he1 := congrArg (fun z => 2*f x*z) (heq x)
    have he2 := congrArg (fun z => 2*t*z) (hev x)
    have he3 := hew x
    dsimp only [u,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    nlinarith [sq_nonneg (f x-g x)]
  have hmax := nonpos_of_weighted_resolvent_subsolution hφ hu ht hsub hI hGI.norm
  intro x
  have hx := hmax x
  change f x ^ 2+(2*t)*v x+(-1 : ℝ)*w x ≤ 0 at hx
  linarith

end KLS
end
