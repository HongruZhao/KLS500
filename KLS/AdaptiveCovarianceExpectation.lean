import KLS.AdaptiveCovarianceExpectationEquation
import KLS.ScalarLinearIntegralEquation

/-! Exact first moment of the covariance of the constructed global adaptive localization. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem covariance_zero_zero_eq_one (hiso : IsIsotropic μ) : covariance μ 0 0 = 1 := by
  ext i j
  change ProbabilityTheory.covariance (fun x : Space n => x i) (fun x => x j) (law μ 0 0) = _
  rw [law_zero_zero, covariance_eq_sub (hiso.memLp_coordinate i) (hiso.memLp_coordinate j)]
  simp only [Pi.mul_apply, hiso.integral_coordinate_mul, hiso.integral_coordinate, mul_zero, sub_zero, Matrix.one_apply]

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

theorem covarianceExpectation_eq_exp_neg (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (i j : Fin n) {T : ℝ} (hT : 0 ≤ T) :
    D.covarianceExpectation i j T = Real.exp (-T) * (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have h := eq_exp_neg_mul_of_integral_equation (D.covarianceExpectation_measurable hμ i j)
    (by positivity : 0 ≤ 2*(supportNormBound hμ)^2) (D.covarianceExpectation_bound hμ i j)
    (fun t ht => D.covarianceExpectation_integral_equation hμ hadm hℱ0 hnull i j ht) hT
  exact h.trans (congrArg (fun a : ℝ => Real.exp (-T)*a)
    (congrFun (congrFun (covariance_zero_zero_eq_one hadm.isotropic) i) j))

theorem covariancePath_integrable (hμ : IsCompact μ.support) (t : ℝ) :
    Integrable (D.covariancePath t) P := by
  have hm : Measurable (D.covariancePath t) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact Measurable.of_uncurry_right (D.covariancePath_entry_measurable hμ i j)
  exact Integrable.of_bound hm.aestronglyMeasurable (2*(supportNormBound hμ)^2)
    (ae_of_all _ fun ω => norm_covariance_le_of_support hμ (supportNormBound_pos hμ).le
      (norm_le_supportNormBound hμ) (D.parameterPath t ω))

/-- This is the Bochner expectation of the actual covariance matrix, with its
integrability derived from compact support and its evolution from Brownian Ito calculus. -/
theorem integral_covariancePath_eq_exp_neg_smul_one (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.covariancePath T ω ∂P) = Real.exp (-T) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  have hc := ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))).integral_comp_comm
      (D.covariancePath_integrable hμ T)
  exact hc.symm.trans (D.covarianceExpectation_eq_exp_neg hμ hadm hℱ0 hnull i j hT)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integral_covariancePath_eq_exp_neg_smul_one
