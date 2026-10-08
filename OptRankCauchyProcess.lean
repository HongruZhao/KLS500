import OptWeightedLowerIntegral
import OptRankCauchyIntegral
import KLS.IntegratedEnergyInfinite

/-! The lower-cumulant product-integrability premise of (92) is discharged
by the proved subset contractions, using only smaller-order compact bounds.
The time-integral estimate is the literal (106) for the constructed process. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n r : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

include hμ hadm hℱ0 hnull

theorem integratedLowerEnergy_le_of_rankWeighted_lower_bounds (hr : 2 ≤ r) {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (qC : ℕ → ℝ) (hqC : ∀ j, 0 ≤ qC j) (qI : ℕ → ℝ) (β : ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (u : Space n)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j (α * qC j * cumulantEnergyMajorant K j))
    (hI : ∀ j, 1 ≤ j → j < r →
      D.integratedEnergy (j+1) u ≤ β * (α * qI j * cumulantEnergyMajorant K j) * ‖u‖^2) :
    D.integratedLowerEnergy r u ≤
      β * α^2 * cumulantEnergyMajorant K r * ‖u‖^2 *
        (∑ j ∈ Finset.Icc 1 (r-2), w j) *
        (∑ j ∈ Finset.Icc 1 (r-2), qI j * qC (r-j) / w j) := by
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull hr α K qC u hC
  have hh := integrated_rankWeighted_lowerCumulant_square_le hμ hadm.isotropic.affineSpan_support_eq_top hr hα hK qC hqC qI β w hw u
    (fun p : Ω × ℝ => D.path p.2 p.1)
    (D.lowerEnergyPath_measurable hμ hadm hr u).aestronglyMeasurable
    (fun T _ => D.energyPath_integrable_prod hμ hadm hℱ0 hnull (by omega) u)
    (D.ae_product_weighted_lower_order_covariance_bounds hμ hadm hℱ0 hnull hr α K qC hC)
    (fun T hT => by
      change (∫ p : Ω × ℝ, D.energyPath (T.card+1) u p.2 p.1 ∂P.prod (volume.restrict (Ici (0 : ℝ)))) ≤ _
      rw [D.integral_prod_energyPath hμ hadm hℱ0 hnull (by omega) u]
      have hT' := mem_activeTailSubsets.mp hT
      exact hI T.card hT'.1 (by omega))
  have he : (∫ p, D.lowerEnergyPath r u p.2 p.1 ∂P.prod (volume.restrict (Ici (0 : ℝ)))) =
      D.integratedLowerEnergy r u := integral_prod_symm _ hL
  exact he ▸ hh

end MaximalProcess
end KLS.AdaptiveLocalization
end
