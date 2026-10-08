import KLS.HessianMetricDivergence
import KLS.WeightedCompactSupport

/-!
# Compact-test integration for the inverse-Hessian diffusion

The pointwise divergence identity is integrated against the genuine density
`exp(-φ)`. Smoothness of the genuine matrix inverse and compact support
discharge every L¹ condition. No invariant-measure identity is assumed.
-/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

/-- Weighted coordinate divergence integrates by parts when its first test
factor is compactly supported. Every product-integrability premise is proved. -/
lemma integral_mul_coordinateDrift_of_hasCompactSupport_left {φ f u : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport f) (i : Fin n) :
    (∫ x, f x * (coordinateDerivative u i x - coordinateDerivative φ i x * u x)
      ∂potentialMeasure φ) =
      -(∫ x, coordinateDerivative f i x * u x ∂potentialMeasure φ) := by
  have hdφ : Continuous (coordinateDerivative φ i) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdf : Continuous (coordinateDerivative f i) :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdu : Continuous (coordinateDerivative u i) :=
    (contDiff_coordinateDerivative hu (m := 0) (by norm_num) i).continuous
  have hfu : Integrable (fun x => f x * u x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hu.continuous) hc.mul_right
  have hdfu : Integrable (fun x => coordinateDerivative f i x * u x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hdf.mul hu.continuous) (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hfdu : Integrable (fun x => f x * coordinateDerivative u i x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hdu) hc.mul_right
  have hfudφ : Integrable (fun x => f x * u x * coordinateDerivative φ i x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hf.continuous.mul hu.continuous).mul hdφ) hc.mul_right.mul_right
  have hi := integral_mul_fderiv_potentialMeasure
    (hφ.differentiable (by norm_num)) (hf.differentiable (by norm_num))
    (hu.differentiable (by norm_num)) (EuclideanSpace.single i 1)
    hfu hdfu hfdu hfudφ
  change (∫ x, f x * coordinateDerivative u i x ∂potentialMeasure φ) =
    (∫ x, f x * u x * coordinateDerivative φ i x ∂potentialMeasure φ) -
      (∫ x, coordinateDerivative f i x * u x ∂potentialMeasure φ) at hi
  have heq : (fun x => f x * (coordinateDerivative u i x - coordinateDerivative φ i x * u x)) =
      fun x => f x * coordinateDerivative u i x - f x * u x * coordinateDerivative φ i x := by
    funext x
    ring
  rw [heq, integral_sub hfdu hfudφ, hi]
  ring

/-- The energy and diffusion integrands really are integrable for a compact
first factor, with no compactness or global boundedness requirement on g. -/
theorem hessianMetricIntegrability_of_hasCompactSupport_left {φ V f g : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport f) :
    Integrable (fun x => f x * hessianMetricDiffusion φ V g x) (potentialMeasure φ) ∧
      Integrable (fun x => ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        coordinateDerivative f i x * coordinateDerivative g j x) (potentialMeasure φ) := by
  have hJ (i j : Fin n) : Continuous (fun x => (coordinateHessian φ x)⁻¹ i j) :=
    (contDiff_inverseHessian_entry hφ hpos i j).continuous
  have hdf (i : Fin n) : Continuous (coordinateDerivative f i) :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdg (i : Fin n) : Continuous (coordinateDerivative g i) :=
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hHg (i j : Fin n) : Continuous (fun x => coordinateHessian g x i j) :=
    (contDiff_coordinateHessian hg (m := 0) (by norm_num) i j).continuous
  have hVg (i : Fin n) : Continuous (fun x => coordinateDerivative V i (gradient φ x)) :=
    (contDiff_coordinateDerivative hV (m := 0) (by norm_num) i).continuous.comp
      (contDiff_gradient hφ (m := 0) (by norm_num)).continuous
  constructor
  · have hL : Continuous (hessianMetricDiffusion φ V g) := by
      unfold hessianMetricDiffusion
      exact (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hJ i j).mul (hHg i j)))).sub
          (continuous_finsetSum _ (fun i _ => (hVg i).mul (hdg i)))
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hL) hc.mul_right
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((hJ i j).mul (hdf i)).mul (hdg j))
      (hasCompactSupport_coordinateDerivative hc i).mul_left.mul_right

/-- The genuine inverse-Hessian diffusion is symmetric against `exp(-φ)`
on smooth tests with compact first factor. No L¹ premise remains. -/
theorem integral_mul_hessianMetricDiffusion_of_hasCompactSupport_left {φ V f g : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport f) :
    (∫ x, f x * hessianMetricDiffusion φ V g x ∂potentialMeasure φ) =
      -(∫ x, ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        coordinateDerivative f i x * coordinateDerivative g j x ∂potentialMeasure φ) := by
  let u (i j : Fin n) (x : Space n) := (coordinateHessian φ x)⁻¹ i j * coordinateDerivative g j x
  have hu (i j : Fin n) : ContDiff ℝ 1 (u i j) :=
    ((contDiff_inverseHessian_entry hφ hpos i j).of_le (by norm_num)).mul
      (contDiff_coordinateDerivative hg (by norm_num) j)
  have hdu (i j : Fin n) : Continuous (coordinateDerivative (u i j) i) :=
    (contDiff_coordinateDerivative (hu i j) (m := 0) (by norm_num) i).continuous
  have hdφ (i : Fin n) : Continuous (coordinateDerivative φ i) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdf (i : Fin n) : Continuous (coordinateDerivative f i) :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hterm (i j : Fin n) : Integrable (fun x => f x *
      (coordinateDerivative (u i j) i x - coordinateDerivative φ i x * u i j x))
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul ((hdu i j).sub ((hdφ i).mul (hu i j).continuous))) hc.mul_right
  have henergy (i j : Fin n) : Integrable (fun x => coordinateDerivative f i x * u i j x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hdf i).mul (hu i j).continuous) (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hpoint (x : Space n) : f x * hessianMetricDiffusion φ V g x =
      ∑ j, ∑ i, f x * (coordinateDerivative (u i j) i x - coordinateDerivative φ i x * u i j x) := by
    rw [hessianMetricDiffusion_eq_sum_divergence hφ hV hpos hMA hg]
    simp only [Finset.mul_sum]
    rfl
  calc
    (∫ x, f x * hessianMetricDiffusion φ V g x ∂potentialMeasure φ) =
        ∫ x, ∑ j, ∑ i, f x * (coordinateDerivative (u i j) i x -
          coordinateDerivative φ i x * u i j x) ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Eventually.of_forall hpoint
    _ = ∑ j, ∑ i, ∫ x, f x * (coordinateDerivative (u i j) i x -
          coordinateDerivative φ i x * u i j x) ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
        (fun i _ => hterm i j))]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum Finset.univ (fun i _ => hterm i j)
    _ = -(∑ j, ∑ i, ∫ x, coordinateDerivative f i x * u i j x ∂potentialMeasure φ) := by
      simp_rw [integral_mul_coordinateDrift_of_hasCompactSupport_left
        (hφ.of_le (by norm_num)) hf (hu _ _) hc, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ j, ∑ i, coordinateDerivative f i x * u i j x ∂potentialMeasure φ) := by
      congr 1
      rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
        (fun i _ => henergy i j))]
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_finsetSum Finset.univ (fun i _ => henergy i j)).symm
    _ = -(∫ x, ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
          coordinateDerivative f i x * coordinateDerivative g j x ∂potentialMeasure φ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u]
      ring

/-- Symmetry is a conclusion for compact C² tests, not a hypothesis. -/
theorem integral_mul_hessianMetricDiffusion_comm {φ V f g : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, f x * hessianMetricDiffusion φ V g x ∂potentialMeasure φ) =
      ∫ x, g x * hessianMetricDiffusion φ V f x ∂potentialMeasure φ := by
  rw [integral_mul_hessianMetricDiffusion_of_hasCompactSupport_left hφ hV hpos hMA
    (hf.of_le (by norm_num)) hg hfc,
    integral_mul_hessianMetricDiffusion_of_hasCompactSupport_left hφ hV hpos hMA
      (hg.of_le (by norm_num)) hf hgc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [((coordinateHessian_symmetric (hφ.of_le (by norm_num)) x).inv).apply i j]
  ring

end KLS
end

#print axioms KLS.integral_mul_coordinateDrift_of_hasCompactSupport_left
#print axioms KLS.hessianMetricIntegrability_of_hasCompactSupport_left
#print axioms KLS.integral_mul_hessianMetricDiffusion_of_hasCompactSupport_left
#print axioms KLS.integral_mul_hessianMetricDiffusion_comm
