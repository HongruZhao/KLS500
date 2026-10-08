import KLS.LocalFamilyNonexplosion

/-! The actual adaptive localization SDE is nonexplosive for compact admissible input. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
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

/-- Infinite lifetime is a conclusion for the process constructed from the
original adaptive drift and inverse-square-root covariance diffusion. -/
theorem ae_lifetime_eq_top (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, D.lifetime ω = ⊤ :=
  D.ae_lifetime_eq_top_of_coefficients_bounded hℱ0 hnull
    (D.ae_finite_horizon_coefficient_bound hμ hadm hℱ0 hnull)

theorem ae_parameterPath_continuousOn_nonneg (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => D.parameterPath t ω) (Ici (0 : ℝ)) := by
  filter_upwards [D.ae_lifetime_eq_top hμ hadm hℱ0 hnull, D.parameterPath_continuousOn] with ω hl hc
  apply hc.mono
  intro t ht
  exact ⟨ht, by rw [hl]; exact WithTop.coe_lt_top t⟩

theorem ae_all_matrix_posSemidef_global (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (D.parameterPath t ω).2.PosSemidef := by
  filter_upwards [D.ae_lifetime_eq_top hμ hadm hℱ0 hnull,
    D.ae_all_matrix_posSemidef hμ hadm.isotropic.affineSpan_support_eq_top] with ω hl hQ t ht
  exact hQ t ht (by rw [hl]; exact WithTop.coe_lt_top t)

theorem ae_all_localizationLaw_logConcave_global (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → measureLogConcave (D.localizationLaw t ω) := by
  filter_upwards [D.ae_lifetime_eq_top hμ hadm hℱ0 hnull,
    D.ae_all_localizationLaw_logConcave hμ hadm] with ω hl hLC t ht
  exact hLC t ht (by rw [hl]; exact WithTop.coe_lt_top t)

end MaximalProcess

/-- Construct a nonexplosive adaptive localization SDE from compact admissible
probability data. The genuine localizing state exits exhaust every finite time;
`IsMaximalLocalSde` supplies the original-coefficient Brownian equations at each exit. -/
theorem exists_adaptiveGlobalProcess (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D ∧
      (∀ᵐ ω ∂P, D.lifetime ω = ⊤) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => D.parameterPath t ω) (Ici (0 : ℝ))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (D.parameterPath t ω).2.PosSemidef) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → measureLogConcave (D.localizationLaw t ω)) := by
  obtain ⟨Ω, mΩ, P, hP, W, D, hD⟩ :=
    exists_adaptiveMaximalLocalProcess μ hμ hadm.isotropic.affineSpan_support_eq_top
  exact ⟨Ω, mΩ, P, hP, W, D, hD,
    D.ae_lifetime_eq_top hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W),
    D.ae_parameterPath_continuousOn_nonneg hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W),
    D.ae_all_matrix_posSemidef_global hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W),
    D.ae_all_localizationLaw_logConcave_global hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W)⟩

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_lifetime_eq_top
#print axioms KLS.AdaptiveLocalization.exists_adaptiveGlobalProcess
