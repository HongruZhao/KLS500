import KLS.C11ScalarComposition
import KLS.HessianMetricSublevelCutoff

open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Shifting the potential does not change its actual gradient. -/
theorem gradient_potentialHeight (u : Space n → ℝ) (x₀ : Space n) :
    gradient (potentialHeight u x₀) = gradient u := by
  funext x
  ext i
  rw [← coordinateDerivative_eq_gradient,← coordinateDerivative_eq_gradient]
  exact coordinateDerivative_potentialHeight u x₀ x i

/-- Actual potential-sublevel cutoffs retain C1 regularity of the source. -/
theorem potentialSublevelCutoff_contDiff_one
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (x₀ : Space n) (c : ℝ) :
    ContDiff ℝ 1 (potentialSublevelCutoff u x₀ c) :=
  ((scaledSublevelProfile_contDiff c).of_le (by simp)).comp (contDiff_potentialHeight hu x₀)

/-- The actual auxiliary tail requires only a C1 source. -/
theorem potentialSublevelTail_contDiff_one
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (x₀ : Space n) (c : ℝ) :
    ContDiff ℝ 1 (potentialSublevelTail u x₀ c) :=
  (scaledSublevelTail_contDiff c).comp (contDiff_potentialHeight hu x₀)

/-- The exact tail derivative identity holds for the original C1 source. -/
theorem coordinateDerivative_potentialSublevelTail_C1
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (x₀ x : Space n) (c : ℝ) (i : Fin n) :
    coordinateDerivative (potentialSublevelTail u x₀ c) i x =
      -(c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖) *
        coordinateDerivative (potentialHeight u x₀) i x := by
  change coordinateDerivative (fun y => scaledSublevelTail c (potentialHeight u x₀ y)) i x = _
  rw [coordinateDerivative_scalar_comp
    ((scaledSublevelTail_contDiff c).differentiable (by norm_num) _)
    ((contDiff_potentialHeight hu x₀).differentiable (by norm_num) _),scaledSublevelTail_deriv]

/-- Every actual coordinate derivative of the cutoff is locally
 Lipschitz, sufficient for genuine weak product tests involving it. -/
theorem coordinateDerivative_potentialSublevelCutoff_locallyLipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (x₀ : Space n) (c : ℝ) (i : Fin n) :
    LocallyLipschitz (coordinateDerivative (potentialSublevelCutoff u x₀ c) i) := by
  have hh := contDiff_potentialHeight hu x₀
  have hGh : LipschitzWith G (gradient (potentialHeight u x₀)) := by
    rwa [gradient_potentialHeight]
  have hη' : ContDiff ℝ 1 (deriv (scaledSublevelProfile c)) :=
    (show ContDiff ℝ (1+1) (scaledSublevelProfile c) from
      (scaledSublevelProfile_contDiff c).of_le (by simp)).deriv'
  have he : coordinateDerivative (potentialSublevelCutoff u x₀ c) i =
      fun x => deriv (scaledSublevelProfile c) (potentialHeight u x₀ x) *
        coordinateDerivative (potentialHeight u x₀) i x := by
    funext x
    exact coordinateDerivative_scalar_comp
      ((scaledSublevelProfile_contDiff c).differentiable (by simp) _)
      (hh.differentiable (by norm_num) x) i
  rw [he]
  exact locallyLipschitz_mul_real (hη'.comp hh).locallyLipschitz
    (lipschitz_coordinateDerivative_of_gradient_lipschitz hGh i).locallyLipschitz

/-- The actual sublevel cutoff diffusion has its two expected terms almost
 everywhere under genuine C1,1 source regularity. -/
theorem hessianMetricDiffusion_potentialSublevelCutoff_ae_C11
    {u : Space n → ℝ} {G : ℝ≥0} (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (V : Space n → ℝ) (x₀ : Space n) (c : ℝ) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c) x =
        c*deriv sublevelCutoffProfile (c*potentialHeight u x₀ x) *
          hessianMetricDiffusion u V (potentialHeight u x₀) x +
        c^2*deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x) *
          inverseHessianGradientForm u (potentialHeight u x₀) x := by
  have hGh : LipschitzWith G (gradient (potentialHeight u x₀)) := by
    rwa [gradient_potentialHeight]
  have ht := hessianMetricDiffusion_scalar_comp_ae_C11 u V
    ((scaledSublevelProfile_contDiff c).of_le (by simp)) (contDiff_potentialHeight hu x₀) hGh
  have he : (fun y => scaledSublevelProfile c (potentialHeight u x₀ y)) =
      potentialSublevelCutoff u x₀ c := rfl
  rw [he] at ht
  simpa only [scaledSublevelProfile_deriv,scaledSublevelProfile_second] using ht

end KLS
end
