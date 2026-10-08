import LevyStochCalc.Brownian.ItoLocality

/-! Brownian integrals respect almost-sure agreement on every nonnegative time. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hW : IsBrownianFiltration W ℱ)

theorem stochasticIntegral_congr_ae_nonneg
    {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → H₁ ω s = H₂ ω s)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hW H₁ hm₁ hp₁ hq₁ T =ᵐ[P]
      stochasticIntegralBrownian W ℱ hW H₂ hm₂ hp₂ hq₂ T := by
  have hz : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) = 0 := by
    calc
      _ = ∫⁻ _ω : Ω, (0 : ℝ≥0∞) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [h] with ω hω
        calc
          _ = ∫⁻ _s in Set.Icc (0 : ℝ) T, (0 : ℝ≥0∞) := by
            apply setLIntegral_congr_fun measurableSet_Icc
            intro s hs
            simp [hω s hs.1]
          _ = 0 := by simp
      _ = 0 := by simp
  have hi := isometry_diff_stochasticIntegralBrownian W ℱ hW H₁ H₂
    hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT
  rw [hz] at hi
  have hmI₁ := ((stochasticIntegralBrownian_stronglyAdapted W ℱ hW H₁ hm₁ hp₁ hq₁ T).mono
    (ℱ.le T)).measurable
  have hmI₂ := ((stochasticIntegralBrownian_stronglyAdapted W ℱ hW H₂ hm₂ hp₂ hq₂ T).mono
    (ℱ.le T)).measurable
  have hae := (lintegral_eq_zero_iff ((((hmI₁.sub hmI₂).nnnorm).coe_nnreal_ennreal).pow_const 2)).mp hi
  filter_upwards [hae] with ω hω
  have hnn : (‖stochasticIntegralBrownian W ℱ hW H₁ hm₁ hp₁ hq₁ T ω -
      stochasticIntegralBrownian W ℱ hW H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using hω
  have hz' : stochasticIntegralBrownian W ℱ hW H₁ hm₁ hp₁ hq₁ T ω -
      stochasticIntegralBrownian W ℱ hW H₂ hm₂ hp₂ hq₂ T ω = 0 := by
    simpa only [ENNReal.coe_eq_zero, nnnorm_eq_zero] using hnn
  exact sub_eq_zero.mp hz'

end KLS.LocalDiffusion
#print axioms KLS.LocalDiffusion.stochasticIntegral_congr_ae_nonneg
