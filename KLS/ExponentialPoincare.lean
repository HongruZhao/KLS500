import KLS.ExponentialPoincareScalar
import KLS.ExponentialDensity
import KLS.LocalRademacher

/-!
# Exact Poincaré constant of the centered exponential law

The scalar locally Lipschitz inequality is transported through the concrete
unit-speed affine embedding. Almost-everywhere differentiability follows
from the proved absolute continuity of the law and local Rademacher.
The upper bound and the existing exponential-test lower bound give exactly
four for this particular original-density-class probability measure.

No universal KLS bound or compact-set class membership is asserted.
-/

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory InnerProductSpace

noncomputable section
namespace KLS.CenteredExponential

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem locallyLipschitz_embedding : LocallyLipschitz embedding := by
  apply ContDiff.locallyLipschitz (𝕂 := ℝ)
  unfold embedding
  fun_prop

/-- Pullback preserves the actual L² requirement of the full test class. -/
theorem memLp_comp_embedding {f : Space 1 → ℝ} (hf : MemLp f 2 measure) :
    MemLp (f ∘ embedding) 2 (expMeasure 1) := by
  exact (memLp_map_measure_iff hf.aestronglyMeasurable
    continuous_embedding.measurable.aemeasurable).mp hf

/-- The centering embedding has derivative equal to the Euclidean unit vector. -/
theorem hasDerivAt_embedding (y : ℝ) :
    HasDerivAt embedding (PiLp.single 2 (0 : Fin 1) (1 : ℝ)) y := by
  let L : ℝ →L[ℝ] Space 1 := coordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
  have hL (r : ℝ) : L r = r • PiLp.single 2 (0 : Fin 1) (1 : ℝ) := by
    ext i
    fin_cases i
    simp [L, coordinateIsometry]
  have hd := L.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_id y).sub_const 1)
  have hfun : (fun z : ℝ => L (z - 1)) = embedding := by
    funext z
    exact hL (z - 1)
  change HasDerivAt (fun z => L (z - 1)) (L 1) y at hd
  rw [hfun, hL, one_smul] at hd
  exact hd

/-- At a differentiability point, the scalar derivative equals the sole gradient coordinate. -/
theorem deriv_comp_embedding_eq {f : Space 1 → ℝ} {y : ℝ}
    (hf : DifferentiableAt ℝ f (embedding y)) :
    deriv (f ∘ embedding) y = gradient f (embedding y) 0 := by
  rw [(hf.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_embedding y)).deriv]
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- Scalar derivative energy and Euclidean gradient energy agree almost everywhere. -/
theorem ae_deriv_comp_embedding_sq {f : Space 1 → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ y ∂expMeasure 1,
      (deriv (f ∘ embedding) y) ^ 2 = ‖gradient f (embedding y)‖ ^ 2 := by
  have hdiff : ∀ᵐ x ∂measure, DifferentiableAt ℝ f x :=
    locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
      hasLogConcaveDensity.absolutelyContinuousLebesgue hf
  have hpull := ae_of_ae_map continuous_embedding.measurable.aemeasurable hdiff
  filter_upwards [hpull] with y hy
  rw [deriv_comp_embedding_eq hy, EuclideanSpace.real_norm_sq_eq]
  simp

/-- Extended variance is preserved exactly under the measurable affine equivalence. -/
theorem variance_eq_comp_embedding (f : Space 1 → ℝ) :
    KLS.variance measure f = ProbabilityTheory.evariance (f ∘ embedding) (expMeasure 1) := by
  change ProbabilityTheory.evariance f ((expMeasure 1).map embeddingEquiv) = _
  simp_rw [ProbabilityTheory.evariance, lintegral_map_equiv, integral_map_equiv,
    embeddingEquiv_apply, Function.comp_apply]

/-- The extended energy formula retains infinite energies. -/
theorem energy_eq_deriv_comp_embedding {f : Space 1 → ℝ} (hf : LocallyLipschitz f) :
    energy measure f = ∫⁻ y, ENNReal.ofReal ((deriv (f ∘ embedding) y) ^ 2) ∂expMeasure 1 := by
  change (∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2)
    ∂(expMeasure 1).map embeddingEquiv) = _
  rw [lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [ae_deriv_comp_embedding_sq hf] with y hy
  rw [embeddingEquiv_apply, hy]

/-- Every locally Lipschitz L² test satisfies the Poincaré inequality with constant four. -/
theorem four_mem_poincareConstants : (4 : ℝ≥0) ∈ poincareConstants measure := by
  intro f hf
  rw [variance_eq_comp_embedding, energy_eq_deriv_comp_embedding hf.1]
  exact ExponentialPoincare.evariance_expMeasure_le
    (hf.1.comp locallyLipschitz_embedding) (memLp_comp_embedding hf.2)

theorem poincareConstant_le_four : poincareConstant measure ≤ 4 :=
  poincareConstant_le_of_mem four_mem_poincareConstants

/-- A genuine exact optimal Poincaré constant for the original density-based KLS example. -/
theorem poincareConstant_eq_four : poincareConstant measure = 4 :=
  le_antisymm poincareConstant_le_four four_le_poincareConstant

/-- The exact example combines established class membership and the proved optimal constant. -/
theorem isKLSMeasure_and_poincareConstant_eq_four :
    IsKLSMeasure measure ∧ poincareConstant measure = 4 :=
  ⟨isKLSMeasure, poincareConstant_eq_four⟩

end KLS.CenteredExponential
end

#print axioms KLS.CenteredExponential.ae_deriv_comp_embedding_sq
#print axioms KLS.CenteredExponential.energy_eq_deriv_comp_embedding
#print axioms KLS.CenteredExponential.four_mem_poincareConstants
#print axioms KLS.CenteredExponential.poincareConstant_eq_four
#print axioms KLS.CenteredExponential.isKLSMeasure_and_poincareConstant_eq_four
