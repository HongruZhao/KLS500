import KLS.IntegratedEnergyFinite
import OptTensorThreeSevenths

/-! Exact drift coefficient from the already established normalized matrix seed. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
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

theorem ae_integrated_energy_inequality_threeSevenths_seed_eight (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, cumulantEnergy μ r u 0 +
      (3/7 : ℝ) * (∫ t in Icc (0 : ℝ) T, D.energyPath (r+1) u t ω ∂volume) ≤
      D.energyPath r u T ω +
      (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * (∫ t in Icc (0 : ℝ) T, D.energyPath r u t ω ∂volume) +
      2 * (∫ t in Icc (0 : ℝ) T, D.energyCrossPath r u t ω ∂volume) -
      D.globalEnergyMartingale hμ hadm hℱ0 hnull r (by omega) u T ω := by
  have hfull := hadm.isotropic.affineSpan_support_eq_top
  have hE := D.ae_continuous_integrablePath hμ hadm hℱ0 hnull
    (contDiff_cumulantEnergy (r := r) hμ hfull u).continuous T
  have hN := D.ae_continuous_integrablePath hμ hadm hℱ0 hnull
    (contDiff_cumulantEnergy (r := r+1) hμ hfull u).continuous T
  have hC := D.ae_continuous_integrablePath hμ hadm hℱ0 hnull
    (continuous_cumulantEnergyCross hμ hfull hr u) T
  have hG := D.ae_continuous_integrablePath hμ hadm hℱ0 hnull
    (continuous_cumulantEnergyDrift hμ hfull hr u) T
  filter_upwards [hE, hN, hC, hG, hseed,
    D.energy_equation_global hμ hadm hℱ0 hnull r (by omega) u hr hT]
    with ω hEω hNω hCω hGω hsω heω
  have hlow : (∫ t in Icc (0 : ℝ) T,
      (3/7 : ℝ) * D.energyPath (r+1) u t ω -
      (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * D.energyPath r u t ω -
      2 * D.energyCrossPath r u t ω ∂volume) ≤
        ∫ t in Icc (0 : ℝ) T, cumulantEnergyDrift μ r u (D.path t ω) ∂volume := by
    apply integral_mono_ae (((hNω.const_mul _).sub (hEω.const_mul _)).sub (hCω.const_mul _)) hGω
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := (cumulantEnergy_drift_lower_threeSevenths hμ hfull hr u _ (hsω t ht.1)).trans_eq
      (cumulantEnergy_generator_exact hμ hfull hr u _)
    exact hh
  change IntegrableOn (fun t => D.energyPath r u t ω) _ at hEω
  change IntegrableOn (fun t => D.energyPath (r+1) u t ω) _ at hNω
  change IntegrableOn (fun t => D.energyCrossPath r u t ω) _ at hCω
  have hsub := integral_sub ((hNω.const_mul (3/7 : ℝ)).sub
    (hEω.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2))))) (hCω.const_mul 2)
  dsimp only [Pi.sub_apply] at hsub
  rw [hsub, integral_sub (hNω.const_mul (3/7 : ℝ)) (hEω.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)))),
    integral_const_mul, integral_const_mul, integral_const_mul] at hlow
  linarith

theorem expected_energy_inequality_finite_threeSevenths_seed_eight (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) {T : ℝ} (hT : 0 < T) :
    cumulantEnergy μ r u 0 +
      (3/7 : ℝ) * (∫ t in Icc (0 : ℝ) T, D.energyExpectation (r+1) u t ∂volume) ≤
      D.energyExpectation r u T +
      (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * (∫ t in Icc (0 : ℝ) T, D.energyExpectation r u t ∂volume) +
      2 * (∫ t in Icc (0 : ℝ) T, ∫ ω, D.energyCrossPath r u t ω ∂P ∂volume) := by
  have hE := D.energyPath_integrable_prod_Icc hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u T
  have hN := D.energyPath_integrable_prod_Icc hμ hadm hℱ0 hnull (show 1 ≤ r+1 by omega) u T
  have hC := D.energyCrossPath_integrable_prod_Icc hμ hadm hℱ0 hnull hr u hL T
  have ht := D.energyPath_integrable hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u hT.le
  have hm := (D.globalEnergyMartingale_martingale hμ hadm hℱ0 hnull r (show 1 ≤ r by omega) u).integrable T
  have hNi : Integrable (fun ω => ∫ t in Icc (0 : ℝ) T, D.energyPath (r+1) u t ω ∂volume) P :=
    hN.integral_prod_left
  have hEi : Integrable (fun ω => ∫ t in Icc (0 : ℝ) T, D.energyPath r u t ω ∂volume) P :=
    hE.integral_prod_left
  have hCi : Integrable (fun ω => ∫ t in Icc (0 : ℝ) T, D.energyCrossPath r u t ω ∂volume) P :=
    hC.integral_prod_left
  have hi := integral_mono_ae
    ((integrable_const (cumulantEnergy μ r u 0)).add (hNi.const_mul (3/7 : ℝ)))
    (((ht.add (hEi.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2))))).add
      (hCi.const_mul 2)).sub hm)
    (D.ae_integrated_energy_inequality_threeSevenths_seed_eight hμ hadm hℱ0 hnull hr u hseed hT)
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  have hsub := integral_sub ((ht.add (hEi.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2))))).add (hCi.const_mul 2)) hm
  have hadd := integral_add (ht.add (hEi.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2))))) (hCi.const_mul 2)
  dsimp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
  rw [integral_add (integrable_const (cumulantEnergy μ r u 0)) (hNi.const_mul (3/7 : ℝ)),
    hsub, hadd,
    integral_add ht (hEi.const_mul ((((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)))), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const,
    D.integral_globalEnergyMartingale_eq_zero hμ hadm hℱ0 hnull r (show 1 ≤ r by omega) u hT.le,
    sub_zero, probReal_univ, one_smul] at hi
  have hNF : (∫ ω, ∫ t in Icc (0 : ℝ) T, D.energyPath (r+1) u t ω ∂volume ∂P) =
      ∫ t in Icc (0 : ℝ) T, D.energyExpectation (r+1) u t ∂volume := integral_integral_swap hN
  have hEF : (∫ ω, ∫ t in Icc (0 : ℝ) T, D.energyPath r u t ω ∂volume ∂P) =
      ∫ t in Icc (0 : ℝ) T, D.energyExpectation r u t ∂volume := integral_integral_swap hE
  have hCF : (∫ ω, ∫ t in Icc (0 : ℝ) T, D.energyCrossPath r u t ω ∂volume ∂P) =
      ∫ t in Icc (0 : ℝ) T, ∫ ω, D.energyCrossPath r u t ω ∂P ∂volume := integral_integral_swap hC
  rw [hNF, hEF, hCF] at hi
  exact hi

end MaximalProcess
end KLS.AdaptiveLocalization
end
