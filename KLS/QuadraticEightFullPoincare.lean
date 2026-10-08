import KLS.ConditionalFullPoincareBound
import KLS.AdaptiveEnergyBase
import KLS.AdaptivePathMatrixSeed

/-! Reduction of the entire proved stochastic induction and full-class
Poincare transfer to the one remaining actual full quadratic-variance input.
This file proves an implication; it does not prove that quadratic input. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem uniformCompactMatrixSeed_of_universalQuadratic {n : ℕ}
    (hQ : ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν) :
    UniformCompactMatrixSeed n := by
  intro μ inst hμ hadm Ω mΩ P instP W D
  exact D.energyMatrixSeed_of_universal_quadratic hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) hQ

theorem compactProcessEnergyBase_of_uniformSeed {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) :
    CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1) := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  have hh := D.expected_energy_base hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) u (hseed μ hμ hadm Ω P W D)
  have hb : cumulantEnergyMajorant 144 1 = (144 : ℝ) := by norm_num [cumulantEnergyMajorant]
  rw [hb]
  nlinarith [sq_nonneg ‖u‖]

theorem universalDirectionalCumulantBound_of_universalQuadratic
    (hQ : ∀ n, ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν)
    {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d (cumulantEnergyMajorant 144 d) := by
  let hseed := fun n => uniformCompactMatrixSeed_of_universalQuadratic (hQ n)
  exact universalDirectionalCumulantBound_of_seed_and_base hseed
    (fun n => compactProcessEnergyBase_of_uniformSeed (hseed n)) hd

theorem weightedCoordinateTaylorBound_sqrt288_of_universalQuadratic
    (hQ : ∀ n, ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν)
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt 288) := by
  let hseed := fun n => uniformCompactMatrixSeed_of_universalQuadratic (hQ n)
  exact weightedCoordinateTaylorBound_sqrt288_of_seed_and_base hseed
    (fun n => compactProcessEnergyBase_of_uniformSeed (hseed n)) hV hμ hκ hlower

theorem admissibleMeasure.poincareConstant_le_of_universalQuadratic
    (hQ : ∀ n, ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν)
    {n : ℕ} (hn : 0 < n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    poincareConstant μ ≤ ENNReal.ofReal 126663739519795200 := by
  let hseed := fun n => uniformCompactMatrixSeed_of_universalQuadratic (hQ n)
  exact hμ.poincareConstant_le_of_uniform_seed_and_base hseed
    (fun n => compactProcessEnergyBase_of_uniformSeed (hseed n)) hn

theorem universalPoincareConstant_le_of_universalQuadratic
    (hQ : ∀ n, ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν) :
    universalPoincareConstant ≤ ENNReal.ofReal 126663739519795200 := by
  let hseed := fun n => uniformCompactMatrixSeed_of_universalQuadratic (hQ n)
  exact universalPoincareConstant_le_of_uniform_seed_and_base hseed
    (fun n => compactProcessEnergyBase_of_uniformSeed (hseed n))

theorem universalPoincareConstant_lt_top_of_universalQuadratic
    (hQ : ∀ n, ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν) :
    universalPoincareConstant < ⊤ :=
  (universalPoincareConstant_le_of_universalQuadratic hQ).trans_lt ENNReal.ofReal_lt_top

end KLS
end
