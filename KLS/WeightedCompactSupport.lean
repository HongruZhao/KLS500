import KLS.WeightedBochner

/-!
# Compactly supported smooth tests satisfy the weighted integration domain

For a continuous finite potential, continuous compactly supported functions
are integrable against the actual density. Derivatives do not enlarge support.
Consequently the diffusion and Bochner identities apply to smooth compactly
supported tests with no separate product-integrability premises.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma integrable_potentialMeasure_of_continuous_hasCompactSupport {φ f : Space n → ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (potentialMeasure φ) := by
  rw [integrable_potentialMeasure_iff hφ.measurable]
  exact (hf.mul (Real.continuous_exp.comp hφ.neg)).integrable_of_hasCompactSupport hc.mul_right

lemma hasCompactSupport_coordinateDerivative {g : Space n → ℝ} (hg : HasCompactSupport g)
    (i : Fin n) : HasCompactSupport (coordinateDerivative g i) :=
  hg.fderiv_apply ℝ (EuclideanSpace.single i 1)

lemma hasCompactSupport_coordinateHessian {g : Space n → ℝ} (hg : HasCompactSupport g)
    (i j : Fin n) : HasCompactSupport (fun x => coordinateHessian g x i j) :=
  hasCompactSupport_coordinateDerivative (hasCompactSupport_coordinateDerivative hg j) i

/-- Compact support of the differentiated test discharges every coordinate L¹ condition. -/
theorem diffusionIntegrability_of_hasCompactSupport {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) : DiffusionIntegrability φ f g := by
  have hdcφ (i : Fin n) : Continuous (coordinateDerivative φ i) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdcf (i : Fin n) : Continuous (coordinateDerivative f i) :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdcg (i : Fin n) : Continuous (coordinateDerivative g i) :=
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hddcg (i : Fin n) : Continuous (fun x => coordinateHessian g x i i) :=
    (contDiff_coordinateHessian hg (m := 0) (by norm_num) i i).continuous
  have hdsc (i : Fin n) : HasCompactSupport (coordinateDerivative g i) :=
    hasCompactSupport_coordinateDerivative hc i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul (hdcg i)) (hdsc i).mul_left
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hdcf i).mul (hdcg i)) (hdsc i).mul_left
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul (hddcg i)) (hasCompactSupport_coordinateHessian hc i i).mul_left
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hf.continuous.mul (hdcg i)).mul (hdcφ i)) (hdsc i).mul_left.mul_right

/-- Smooth compactly supported tests lie in the actual Bochner integration domain. -/
theorem bochnerIntegrability_of_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    BochnerIntegrability φ g := by
  refine ⟨?_, ?_, ?_⟩
  · exact diffusionIntegrability_of_hasCompactSupport (hφ.of_le (by norm_num))
      (contDiff_weightedDiffusion hφ hg) (hg.of_le (by norm_num)) hc
  · intro i
    have hgi : ContDiff ℝ 2 (coordinateDerivative g i) :=
      contDiff_coordinateDerivative hg (by norm_num) i
    exact diffusionIntegrability_of_hasCompactSupport (hφ.of_le (by norm_num))
      (hgi.of_le (by norm_num)) hgi (hasCompactSupport_coordinateDerivative hc i)
  · intro i j
    have hdci : Continuous (coordinateDerivative g i) :=
      (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
    have hdcj : Continuous (coordinateDerivative g j) :=
      (contDiff_coordinateDerivative hg (m := 0) (by norm_num) j).continuous
    have hh : Continuous (fun x => coordinateHessian φ x i j) :=
      (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hh.mul hdci).mul hdcj) (hasCompactSupport_coordinateDerivative hc i).mul_left.mul_right

/-- The diffusion identity now has only smoothness and compact support as test hypotheses. -/
theorem integral_mul_weightedDiffusion_of_hasCompactSupport {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) :
    (∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) :=
  integral_mul_weightedDiffusion (hφ.differentiable (by norm_num))
    (hf.differentiable (by norm_num))
    (fun i => (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).differentiable
      (by norm_num)) (diffusionIntegrability_of_hasCompactSupport hφ hf hg hc)

/-- The integrated Bochner identity for every C³ compactly supported test and C² potential. -/
theorem integral_weightedDiffusion_sq_of_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) =
      (∫ x, hessianSquare g x ∂potentialMeasure φ) +
        ∫ x, hessianGradientForm φ g x ∂potentialMeasure φ :=
  integral_weightedDiffusion_sq_eq_sum hφ hg (bochnerIntegrability_of_hasCompactSupport hφ hg hc)

end KLS
end

#print axioms KLS.integrable_potentialMeasure_of_continuous_hasCompactSupport
#print axioms KLS.diffusionIntegrability_of_hasCompactSupport
#print axioms KLS.bochnerIntegrability_of_hasCompactSupport
#print axioms KLS.integral_mul_weightedDiffusion_of_hasCompactSupport
#print axioms KLS.integral_weightedDiffusion_sq_of_hasCompactSupport
