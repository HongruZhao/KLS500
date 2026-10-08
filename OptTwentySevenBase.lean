import OptTwentySevenConvolution
import OptRankCauchyInduction

/-! The first sixteen degrees enter the all-rank argument through their
already established actual compact and integrated energy estimates. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.RouteArithmetic
set_option maxHeartbeats 2000000

theorem twentySeven_base_coefficients (d : ℕ) (hd : 1 ≤ d) (hd16 : d ≤ 16) :
    (rankCauchyCumulantWeight d ≤
      (43/2000 : ℝ)*twentySevenCumulantWeight d*(27)^d) ∧
    (rankCauchyIntegralWeight d ≤
      (13/125 : ℝ)*twentySevenIntegralWeight d*(27)^d) := by
  interval_cases d <;> norm_num [twentySevenCumulantWeight, twentySevenIntegralWeight]

end KLS.RouteArithmetic
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantAndIntegratedEnergyBound_twentySeven_base {n d : ℕ}
    (hseed : UniformCompactMatrixSeed n) (hd : 1 ≤ d) (hd16 : d ≤ 16) :
    CompactCumulantEnergyBound n d
      ((43/2000 : ℝ)*twentySevenCumulantWeight d*cumulantEnergyMajorant (27) d) ∧
    CompactProcessScaledIntegratedEnergyBound n d
      ((13/125 : ℝ)*twentySevenIntegralWeight d*cumulantEnergyMajorant (27) d) 1 := by
  have hb := compactCumulantAndIntegratedEnergyBound_rankCauchy hseed d hd hd16
  have hs := RouteArithmetic.twentySeven_base_coefficients d hd hd16
  have hC : rankCauchyCumulantWeight d*cumulantEnergyMajorant 1 d ≤
      (43/2000 : ℝ)*twentySevenCumulantWeight d*cumulantEnergyMajorant (27) d := by
    have hh := mul_le_mul_of_nonneg_right hs.1 (sq_nonneg (d.factorial : ℝ))
    simpa only [cumulantEnergyMajorant, one_pow, one_mul, mul_assoc] using hh
  have hI : rankCauchyIntegralWeight d*cumulantEnergyMajorant 1 d ≤
      (13/125 : ℝ)*twentySevenIntegralWeight d*cumulantEnergyMajorant (27) d := by
    have hh := mul_le_mul_of_nonneg_right hs.2 (sq_nonneg (d.factorial : ℝ))
    simpa only [cumulantEnergyMajorant, one_pow, one_mul, mul_assoc] using hh
  constructor
  · intro μ hμ hadm u
    exact (hb.1 μ hμ hadm u).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  · intro μ inst hμ hadm Ω mΩ P instP W D u
    have hh := hb.2 μ hμ hadm Ω P W D u
    simpa only [one_mul] using hh.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 1)) (sq_nonneg ‖u‖))

end KLS.AdaptiveLocalization
end
