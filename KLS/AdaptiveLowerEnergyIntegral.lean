import KLS.IntegratedLowerContraction
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

theorem ae_product_lower_order_covariance_bounds (hr : 2 ≤ r) (K : ℝ)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j (cumulantEnergyMajorant K j)) :
    ∀ᵐ p ∂P.prod (volume.restrict (Ici (0 : ℝ))), ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (D.path p.2 p.1) ≤ cumulantEnergyMajorant K Tᶜ.card *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (D.path p.2 p.1)) v) := by
  have hLC := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := volume.restrict (Ici (0 : ℝ)))).ae
    (D.ae_all_localizationLaw_logConcave_global hμ hadm hℱ0 hnull)
  have htime := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := volume.restrict (Ici (0 : ℝ)))).ae
    (ae_restrict_mem measurableSet_Ici)
  filter_upwards [hLC, htime] with p hp ht T hT v
  have hcard : T.card + Tᶜ.card = r := by simp
  have hT' := mem_activeTailSubsets.mp hT
  exact cumulantEnergy_le_of_compactBound hμ hadm.isotropic.affineSpan_support_eq_top
    (by omega) v (D.path p.2 p.1) (hp p.2 ht) (hC _ (by omega) (by omega))

theorem lowerEnergyPath_integrable_of_lower_compact_bounds (hr : 2 ≤ r) (K : ℝ)
    (u : Space n)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j (cumulantEnergyMajorant K j)) :
    Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ)))) := by
  exact lowerCumulant_square_integrable hμ hadm.isotropic.affineSpan_support_eq_top hr K u
    (fun p : Ω × ℝ => D.path p.2 p.1)
    (D.lowerEnergyPath_measurable hμ hadm hr u).aestronglyMeasurable
    (fun T _ => D.energyPath_integrable_prod hμ hadm hℱ0 hnull (by omega) u)
    (D.ae_product_lower_order_covariance_bounds hμ hadm hℱ0 hnull hr K hC)

theorem integratedLowerEnergy_le_of_lower_bounds (hr : 2 ≤ r) {K : ℝ} (hK : 0 < K)
    (u : Space n)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j (cumulantEnergyMajorant K j))
    (hI : ∀ j, 1 ≤ j → j < r →
      D.integratedEnergy (j+1) u ≤ 2 * cumulantEnergyMajorant K j * ‖u‖^2) :
    D.integratedLowerEnergy r u ≤
      2 * ((r-2 : ℕ) : ℝ)^2 * cumulantEnergyMajorant K r * ‖u‖^2 := by
  have hL := D.lowerEnergyPath_integrable_of_lower_compact_bounds hμ hadm hℱ0 hnull hr K u hC
  have hh := integrated_lowerCumulant_square_le hμ hadm.isotropic.affineSpan_support_eq_top hr hK u
    (fun p : Ω × ℝ => D.path p.2 p.1)
    (D.lowerEnergyPath_measurable hμ hadm hr u).aestronglyMeasurable
    (fun T _ => D.energyPath_integrable_prod hμ hadm hℱ0 hnull (by omega) u)
    (D.ae_product_lower_order_covariance_bounds hμ hadm hℱ0 hnull hr K hC)
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
