import KLS.AdaptiveMaximalSmoothIto

/-! Actual cumulant energy satisfies the local Itô equation with a genuine
martingale, and the actual exits exhaust every finite time. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def cumulantEnergyDrift (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  -((r+2 : ℕ) : ℝ) * cumulantEnergy μ r u z -
    2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) +
    ∑ k, energyNoiseCorrection (whitenedCumulantTensor μ r u z)
      (whitenedCovarianceNoiseMatrix μ k z) (whitenedNextCumulantTensor μ r u k z)

theorem cumulantEnergy_zero (hiso : IsIsotropic μ) (r : ℕ) (u : Space n) :
    cumulantEnergy μ r u 0 =
      ∑ a : Fin r → Fin n, (cumulantTensor μ (r+1) (cumulantSliceDirections u a))^2 := by
  unfold cumulantEnergy coordinateCovarianceMatrix
  simp only [decodeState_zero, Prod.fst_zero, Prod.snd_zero, covariance_zero_zero_eq_one hiso,
    tensorMetric_one, coordinateCumulantTensor, coordinateCumulant, law_zero_zero, dotProduct, pow_two]

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def energyPath (r : ℕ) (u : Space n) (t : ℝ) (ω : Ω) : ℝ :=
  cumulantEnergy μ r u (D.path t ω)

def energyMartingale (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤)
    (r : ℕ) (u : Space n) (j : ℕ) : ℝ → Ω → ℝ :=
  D.smoothMartingale (cumulantEnergy μ r u) (contDiff_cumulantEnergy hμ hfull u) j

theorem energyMartingale_martingale (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (r : ℕ) (u : Space n) (j : ℕ) :
    Martingale (D.energyMartingale hμ hfull r u j) ℱ P :=
  D.smoothMartingale_martingale _ _ j

theorem energyMartingale_zero (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (r : ℕ) (u : Space n) (j : ℕ) :
    D.energyMartingale hμ hfull r u j 0 =ᵐ[P] 0 := D.smoothMartingale_zero _ _ j

/-- The literal current-law energy has drift (89) and an actual Brownian
martingale up to each genuine state exit. -/
theorem energy_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 2 ≤ r) (u : Space n) (j : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit j ω →
      D.energyPath r u T ω - cumulantEnergy μ r u 0 =
        (∫ t in Icc (0 : ℝ) T, cumulantEnergyDrift μ r u (D.path t ω) ∂volume) +
          D.energyMartingale hμ hfull r u j T ω := by
  have he := D.smoothObservable_equation (cumulantEnergy μ r u)
    (contDiff_cumulantEnergy hμ hfull u) hℱ0 hnull j hT
  simp_rw [cumulantEnergy_generator_exact hμ hfull hr u] at he
  exact he

end MaximalProcess

/-- The energy process and its exhausting local martingales are constructed
from compact admissible input, with no supplied energy dynamics. -/
theorem exists_adaptiveCumulantEnergyProcess (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D ∧
      (∀ᵐ ω ∂P, D.lifetime ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, ∃ j : ℕ, (T : WithTop ℝ) < D.exit j ω) ∧
      (∀ (r : ℕ) (u : Space n) (j : ℕ),
        Martingale (D.energyMartingale hμ hadm.isotropic.affineSpan_support_eq_top r u j)
          (usualFiltration W) P) ∧
      (∀ (r : ℕ) (hr : 2 ≤ r) (u : Space n) (j : ℕ) (T : ℝ),
        0 < T → ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit j ω →
          D.energyPath r u T ω - cumulantEnergy μ r u 0 =
            (∫ t in Icc (0 : ℝ) T, cumulantEnergyDrift μ r u (D.path t ω) ∂volume) +
              D.energyMartingale hμ hadm.isotropic.affineSpan_support_eq_top r u j T ω) := by
  obtain ⟨Ω, mΩ, P, hP, W, D, hD, htop, _⟩ := exists_adaptiveGlobalProcess μ hμ hadm
  exact ⟨Ω, mΩ, P, hP, W, D, hD, htop,
    D.ae_cumulant_exits_exhaust hμ hadm (usualFiltration_beforeZero W) (usualFiltration_null W),
    fun r u j => D.energyMartingale_martingale hμ hadm.isotropic.affineSpan_support_eq_top r u j,
    fun r hr u j T hT => D.energy_equation hμ hadm.isotropic.affineSpan_support_eq_top
      (usualFiltration_beforeZero W) (usualFiltration_null W) r hr u j hT⟩

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.energy_equation
#print axioms KLS.AdaptiveLocalization.exists_adaptiveCumulantEnergyProcess
