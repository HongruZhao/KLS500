import KLS.AdaptiveNonexplosion

/-! Compact support and the proved normalized moments uniformly bound actual covariance noise. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def covarianceUniformNoiseBound (hμ : IsCompact μ.support) : ℝ :=
  4*(supportNormBound hμ)^2 * (isotropicTailRadius n * geometricNormMomentConstant 1)

omit [IsProbabilityMeasure μ] in
theorem covarianceUniformNoiseBound_nonneg (hμ : IsCompact μ.support) :
    0 ≤ covarianceUniformNoiseBound hμ := by
  unfold covarianceUniformNoiseBound
  exact mul_nonneg (by positivity) (mul_nonneg (isotropicTailRadius_pos n).le
    (geometricNormMomentConstant_pos 1).le)

/-- The bound concerns the literal covariance noise, not an assumed martingale coefficient. -/
theorem abs_covarianceNoiseCoefficient_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) (i j k : Fin n) :
    |covarianceNoiseCoefficient μ i j k z| ≤ covarianceUniformNoiseBound hμ := by
  let p := decodeState z
  let ν := law μ p.1 p.2
  let y := normalizedCenteredVector ν
  let R := supportNormBound hμ
  have hR : 0 ≤ R := (supportNormBound_pos hμ).le
  haveI : IsProbabilityMeasure ν := law_isProbability hμ p.1 p.2
  have hm : ‖mean μ p.1 p.2‖ ≤ R :=
    norm_mean_le_of_support hμ hR (norm_le_supportNormBound hμ) p
  have hc (x : Space n) (hx : ‖x‖ ≤ R) (a : Fin n) : |x a - mean μ p.1 p.2 a| ≤ 2*R := by
    calc
      _ ≤ |x a| + |mean μ p.1 p.2 a| := abs_sub _ _
      _ ≤ R+R := add_le_add ((PiLp.norm_apply_le _ _).trans hx)
        ((norm_le_pi_norm (mean μ p.1 p.2) a).trans hm)
      _ = _ := by ring
  have hyint : Integrable (fun x => ‖y x‖) ν := by
    simpa only [pow_one] using hlc.integrable_normalizedCenteredVector_norm_pow 1
  have hyle : (∫ x, ‖y x‖ ∂ν) ≤ isotropicTailRadius n * geometricNormMomentConstant 1 := by
    have hp : (covarianceMatrix ν).PosDef := by
      rw [← covariance_eq_covarianceMatrix hμ p]
      exact covariance_posDef hμ hfull p
    simpa only [pow_one] using hlc.integral_normalizedCenteredVector_norm_pow_le hp 1
  have hnoise : covarianceNoiseCoefficient μ i j k z =
      ∫ x, (x i - mean μ p.1 p.2 i)*(x j - mean μ p.1 p.2 j)*y x k ∂ν :=
    covarianceNoiseMatrix_eq_integral hμ z i j k
  rw [hnoise]
  calc
    _ ≤ ∫ x, ‖(x i-mean μ p.1 p.2 i)*(x j-mean μ p.1 p.2 j)*y x k‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, (4*R^2)*‖y x‖ ∂ν := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hyint.const_mul _)
      filter_upwards [ae_norm_le_law hμ (norm_le_supportNormBound hμ) p] with x hx
      rw [norm_mul, norm_mul]
      have hprod := mul_le_mul (hc x hx i) (hc x hx j) (abs_nonneg _) (by positivity : 0 ≤ 2*R)
      have hyk := PiLp.norm_apply_le (y x) k
      calc
        _ ≤ (2*R*(2*R))*‖y x‖ := mul_le_mul hprod hyk (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 4*R^2*(∫ x, ‖y x‖ ∂ν) := integral_const_mul _ _
    _ ≤ covarianceUniformNoiseBound hμ := mul_le_mul_of_nonneg_left hyle (by positivity)

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.abs_covarianceNoiseCoefficient_le
