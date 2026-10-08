import KLS.CumulantEnergyBase

/-! Equation (78) for the actual localization process. The first energy is
exactly covariance, and the literal matrix seed controls the integrated next
energy by eight times the original squared direction norm. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

include hμ hadm hℱ0 hnull

omit hℱ0 hnull in
theorem energyPath_one_eq_covariance (u : Space n) (t : ℝ) (ω : Ω) :
    D.energyPath 1 u t ω = D.directionalCovariancePath u t ω := by
  rw [energyPath, cumulantEnergy_one_eq_covariance hμ hadm.isotropic.affineSpan_support_eq_top,
    directionalCovariancePath, directionalCovarianceCLM_apply]
  rfl

theorem energyExpectation_one (u : Space n) {t : ℝ} (ht : 0 ≤ t) :
    D.energyExpectation 1 u t = Real.exp (-t) * ‖u‖^2 := by
  unfold energyExpectation
  simp_rw [D.energyPath_one_eq_covariance hμ hadm]
  exact D.integral_directionalCovariancePath hμ hadm hℱ0 hnull u ht

omit hℱ0 hnull in
theorem ae_all_energyPath_two_le_eight_covariance (u : Space n) (hseed : D.EnergyMatrixSeed) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.energyPath 2 u t ω ≤
      8 * D.directionalCovariancePath u t ω := by
  filter_upwards [hseed] with ω hs t ht
  exact (cumulantEnergy_two_le_eight_covariance hμ hadm.isotropic.affineSpan_support_eq_top
    u (D.path t ω) (hs t ht)).trans_eq
      (congrArg (8 * ·) (directionalCovarianceCLM_apply u _).symm)

theorem energyExpectation_two_le_eight_exp_neg (u : Space n)
    (hseed : D.EnergyMatrixSeed) {t : ℝ} (ht : 0 ≤ t) :
    D.energyExpectation 2 u t ≤ 8 * Real.exp (-t) * ‖u‖^2 := by
  calc
    _ ≤ ∫ ω, 8 * D.directionalCovariancePath u t ω ∂P :=
      integral_mono_ae (D.energyPath_integrable hμ hadm hℱ0 hnull (by omega) u ht)
        ((D.directionalCovariancePath_integrable hμ u t).const_mul _)
        ((D.ae_all_energyPath_two_le_eight_covariance hμ hadm u hseed).mono fun _ h => h t ht)
    _ = _ := by
      rw [integral_const_mul, D.integral_directionalCovariancePath hμ hadm hℱ0 hnull u ht]
      ring

theorem integratedEnergy_two_le_eight (u : Space n) (hseed : D.EnergyMatrixSeed) :
    D.integratedEnergy 2 u ≤ 8 * ‖u‖^2 := by
  unfold integratedEnergy
  rw [integral_Ici_eq_integral_Ioi]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (8 * ‖u‖^2) * Real.exp (-t) ∂volume := by
      apply integral_mono_ae (D.integrable_energyExpectation_Ioi hμ hadm hℱ0 hnull (by omega) u)
        ((integrableOn_exp_neg_Ioi 0).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (D.energyExpectation_two_le_eight_exp_neg hμ hadm hℱ0 hnull u hseed ht.le).trans_eq (by ring)
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- The actual base step (78), with arbitrary fixed direction and only the
paper's literal matrix seed left as a hypothesis. -/
theorem expected_energy_base (u : Space n) (hseed : D.EnergyMatrixSeed) :
    cumulantEnergy μ 1 u 0 + (1/2 : ℝ) * D.integratedEnergy 2 u ≤ 5 * ‖u‖^2 := by
  rw [cumulantEnergy_one_zero hμ hadm.isotropic]
  have hb := D.integratedEnergy_two_le_eight hμ hadm hℱ0 hnull u hseed
  linarith

end MaximalProcess
end KLS.AdaptiveLocalization
end
