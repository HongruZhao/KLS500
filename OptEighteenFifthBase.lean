import OptEighteenFifthConvolution
import OptRankSymmetric128Induction

set_option maxRecDepth 8192

/-! The first sixteen degrees enter the all-rank argument through their
already established actual compact and integrated energy estimates. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.RouteArithmetic
set_option maxHeartbeats 2000000

theorem eighteenFifth_base_coefficients (d : ℕ) (hd : 1 ≤ d) (hd128 : d ≤ 128) :
    (rankSymmetric128CumulantWeight d ≤
      (63/500 : ℝ)*eighteenFifthCumulantWeight d*(91/5)^d) ∧
    (rankSymmetric128IntegralWeight d ≤
      (9/20 : ℝ)*eighteenFifthIntegralWeight d*(91/5)^d) := by
  interval_cases d <;> norm_num [eighteenFifthCumulantWeight, eighteenFifthIntegralWeight]

end KLS.RouteArithmetic
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantAndIntegratedEnergyBound_eighteenFifth_base {n d : ℕ}
    (hseed : UniformCompactMatrixSeed n) (hcubic : UniformCompactCubicSeed n) (hd : 1 ≤ d) (hd128 : d ≤ 128) :
    CompactCumulantEnergyBound n d
      ((63/500 : ℝ)*eighteenFifthCumulantWeight d*cumulantEnergyMajorant (91/5) d) ∧
    CompactProcessScaledIntegratedEnergyBound n d
      ((9/20 : ℝ)*eighteenFifthIntegralWeight d*cumulantEnergyMajorant (91/5) d) 1 := by
  have hb := compactCumulantAndIntegratedEnergyBound_rankSymmetric128 hseed hcubic d hd hd128
  have hs := RouteArithmetic.eighteenFifth_base_coefficients d hd hd128
  have hC : rankSymmetric128CumulantWeight d*cumulantEnergyMajorant 1 d ≤
      (63/500 : ℝ)*eighteenFifthCumulantWeight d*cumulantEnergyMajorant (91/5) d := by
    have hh := mul_le_mul_of_nonneg_right hs.1 (sq_nonneg (d.factorial : ℝ))
    simpa only [cumulantEnergyMajorant, one_pow, one_mul, mul_assoc] using hh
  have hI : rankSymmetric128IntegralWeight d*cumulantEnergyMajorant 1 d ≤
      (9/20 : ℝ)*eighteenFifthIntegralWeight d*cumulantEnergyMajorant (91/5) d := by
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
