import KLS.AdaptiveGlobalCovarianceEquation

/-! Fubini and zero-mean genuine Brownian noise give the covariance expectation integral equation. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def covarianceExpectation (i j : Fin n) (t : ℝ) : ℝ := ∫ ω, D.covariancePath t ω i j ∂P

theorem covariancePath_entry_bound (hμ : IsCompact μ.support) (i j : Fin n) (t : ℝ) (ω : Ω) :
    |D.covariancePath t ω i j| ≤ 2*(supportNormBound hμ)^2 :=
  ((norm_le_pi_norm (D.covariancePath t ω i) j).trans (norm_le_pi_norm (D.covariancePath t ω) i)).trans
    (norm_covariance_le_of_support hμ (supportNormBound_pos hμ).le (norm_le_supportNormBound hμ) _)

theorem covariancePath_entry_measurable (hμ : IsCompact μ.support) (i j : Fin n) :
    Measurable (Function.uncurry fun ω t => D.covariancePath t ω i j) :=
  (contDiff_coordinateCovariance hμ i j).continuous.measurable.comp D.measurable_path

theorem covariancePath_entry_integrable (hμ : IsCompact μ.support) (i j : Fin n) (t : ℝ) :
    Integrable (fun ω => D.covariancePath t ω i j) P :=
  Integrable.of_bound (Measurable.of_uncurry_right (D.covariancePath_entry_measurable hμ i j)).aestronglyMeasurable
    (2*(supportNormBound hμ)^2) (ae_of_all _ fun ω => D.covariancePath_entry_bound hμ i j t ω)

theorem covariancePath_entry_integrable_prod (hμ : IsCompact μ.support) (i j : Fin n) (T : ℝ) :
    Integrable (Function.uncurry fun ω t => D.covariancePath t ω i j) (P.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  Integrable.of_bound (D.covariancePath_entry_measurable hμ i j).aestronglyMeasurable
    (2*(supportNormBound hμ)^2) (ae_of_all _ fun p => D.covariancePath_entry_bound hμ i j p.2 p.1)

theorem covarianceExpectation_measurable (hμ : IsCompact μ.support) (i j : Fin n) :
    Measurable (D.covarianceExpectation i j) :=
  (D.covariancePath_entry_measurable hμ i j).stronglyMeasurable.integral_prod_left.measurable

theorem covarianceExpectation_bound (hμ : IsCompact μ.support) (i j : Fin n) (t : ℝ) :
    |D.covarianceExpectation i j t| ≤ 2*(supportNormBound hμ)^2 := by
  calc
    _ ≤ ∫ ω, ‖D.covariancePath t ω i j‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _ω : Ω, 2*(supportNormBound hμ)^2 ∂P :=
      integral_mono (D.covariancePath_entry_integrable hμ i j t).norm (integrable_const _)
        (fun ω => D.covariancePath_entry_bound hμ i j t ω)
    _ = _ := by simp

theorem covarianceExpectation_initial (i j : Fin n) : D.covarianceExpectation i j 0 = covariance μ 0 0 i j := by
  have he : (fun ω => D.covariancePath 0 ω i j) =ᵐ[P] fun _ => covariance μ 0 0 i j := by
    filter_upwards [D.parameterPath_initial] with ω h0
    unfold covariancePath
    rw [h0]
    rfl
  exact (integral_congr_ae he).trans (by simp)

/-- The expectation solves the actual drift equation; exchange of integrals is
justified by a uniform compact-support bound on the covariance itself. -/
theorem covarianceExpectation_integral_equation (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (i j : Fin n) {T : ℝ} (hT : 0 ≤ T) :
    D.covarianceExpectation i j T = covariance μ 0 0 i j -
      ∫ t in Icc (0 : ℝ) T, D.covarianceExpectation i j t ∂volume := by
  rcases eq_or_lt_of_le hT with h | h
  · subst T
    simpa using D.covarianceExpectation_initial i j
  have hnoise (k : Fin n) : Integrable (D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T) P :=
    (D.globalCovarianceNoiseIntegral_martingale hμ hadm hℱ0 hnull i j k).integrable T
  have hprod := D.covariancePath_entry_integrable_prod hμ i j T
  have hDrift : Integrable (fun ω => ∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) P :=
    hprod.integral_prod_left
  have hSum : Integrable (fun ω => ∑ k : Fin n, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω) P :=
    integrable_finsetSum _ fun k _ => hnoise k
  have hInt := integral_congr_ae (D.covariance_equation_global hμ hadm hℱ0 hnull i j h)
  have hL : (∫ ω, D.covariancePath T ω i j - covariance μ 0 0 i j ∂P) =
      D.covarianceExpectation i j T - covariance μ 0 0 i j := by
    rw [integral_sub (D.covariancePath_entry_integrable hμ i j T) (integrable_const _)]
    simp [covarianceExpectation]
  have hSum0 : (∫ ω, ∑ k : Fin n, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun k _ => hnoise k)]
    simp only [D.integral_globalCovarianceNoiseIntegral_eq_zero hμ hadm hℱ0 hnull i j _ hT,
      Finset.sum_const_zero]
  have hSwap : (∫ ω, ∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume ∂P) =
      ∫ t in Icc (0 : ℝ) T, D.covarianceExpectation i j t ∂volume := integral_integral_swap hprod
  have hR : (∫ ω, -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) +
      ∑ k : Fin n, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω ∂P) =
      -(∫ t in Icc (0 : ℝ) T, D.covarianceExpectation i j t ∂volume) := by
    calc
      _ = (∫ ω, -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) ∂P) +
          ∫ ω, ∑ k : Fin n, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω ∂P :=
        integral_add hDrift.neg hSum
      _ = _ := by rw [hSum0, add_zero, integral_neg, hSwap]
  have heq := hL.symm.trans (hInt.trans hR)
  linarith

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.covarianceExpectation_integral_equation
