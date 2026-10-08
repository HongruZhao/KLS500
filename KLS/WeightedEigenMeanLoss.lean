import KLS.WeightedIterationMeanTaylor
import KLS.FirstMixedMomentContraction
import KLS.WeightedIterationStoppingIndex
import KLS.ThirdCumulant

/-! The initial mean loss is bounded from the genuine normalized eigenfunction
and actual directional second moments, rather than postulated. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

omit [IsProbabilityMeasure (potentialMeasure φ)] in
theorem memLp_coordinate_potentialMeasure (j : Fin n) :
    MemLp (fun x : Space n => x j) 2 (potentialMeasure φ) := by
  have hn : MemLp (fun x : Space n => ‖x‖) 2 (potentialMeasure φ) := by
    simpa using memLp_norm_pow_mul_exp_norm_potentialMeasure hφ hκ hlower 1 0
  exact hn.mono' (by fun_prop) (.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_norm] using PiLp.norm_apply_le x j)

theorem eigen_mean_gradient_sq_le {f : Space n → ℝ} {lam : ℝ}
    (hf : ContDiff ℝ 2 f) (hf2 : MemLp f 2 (potentialMeasure φ))
    (hm : ∫ x, f x ∂potentialMeasure φ = 0)
    (hu : ∫ x, f x ^ 2 ∂potentialMeasure φ = 1)
    (heigen : ∀ x, weightedDiffusion φ f x = -lam * f x)
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (hsecond : ∀ v : Space n, (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2) :
    (∑ j : Fin n, (∫ x, coordinateDerivative f j x ∂potentialMeasure φ) ^ 2) ≤ lam ^ 2 := by
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    convert hf2.const_mul (-lam) using 1
    exact funext heigen
  have heq : -weightedDiffusion φ f = fun x => lam * f x := by
    funext x
    simp only [Pi.neg_apply, heigen]
    ring
  have hc (j : Fin n) : (∫ x, coordinateDerivative f j x ∂potentialMeasure φ) =
      lam * (∫ x, f x * x j ∂potentialMeasure φ) := by
    rw [← weightedDiffusion_exponentialTiltCoordinateTaylor_one hφ hκ hlower hf hL hG (fun _ => j),
      heq, exponentialTiltCoordinateTaylor_const_mul hφ hκ hlower hf2,
      exponentialTiltCoordinateTaylor_one_of_integral_eq_zero hφ hκ hlower hf2 hm]
  simp_rw [hc, mul_pow]
  rw [← Finset.mul_sum]
  have hb := firstMixedMomentVector_norm_sq_le_one hf2
    (memLp_coordinate_potentialMeasure hφ hκ hlower) hu hsecond
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg lam)).trans_eq (mul_one _)

theorem weightedEigenIteration_initial_meanLoss_le (U : WeightedCenteredH1 φ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hV : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ))
    (hU : ‖weightedH1Value φ U‖ = 1) {lam : ℝ}
    (heigen : ∀ x, weightedDiffusion φ f x = -lam * f x)
    (hsecond : ∀ v : Space n, (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2) :
    weightedIterationMeanLoss hφ hκ hlower (weightedSingleFamily U) 0 ≤ lam ^ 2 := by
  have hvμ : (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ] f :=
    (withDensity_absolutelyContinuous _ _).ae_eq hV.symm
  have hf2 := (Lp.memLp (weightedH1Value φ U)).ae_eq hvμ
  have hm : (∫ x, f x ∂potentialMeasure φ) = 0 := by
    rw [integral_congr_ae hvμ.symm, weightedH1_integral_eq_zero hφ.continuous U]
  have hu := realLp_norm_sq_eq_integral_sq_of_ae hvμ
  rw [hU, one_pow] at hu
  have hb := eigen_mean_gradient_sq_le hφ hκ hlower hf hf2 hm hu.symm heigen
    (weightedH1_integrable_gradient_norm_sq_of_representative
      (hφ.of_le (by norm_num)) U (hf.of_le (by norm_num)) hV) hsecond
  unfold weightedIterationMeanLoss
  change (∑ ji : Fin n × Fin 1,
    (∫ x, weightedH1Derivative φ ji.1 U x ∂potentialMeasure φ) ^ 2) ≤ lam ^ 2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply integral_congr_ae
  exact ((withDensity_absolutelyContinuous _ _).ae_eq
    (weightedH1_coordinateDerivative_of_representative
      (hφ.of_le (by norm_num)) U (hf.of_le (by norm_num)) hV j)).symm

theorem weightedEigenIteration_initial_meanLoss_le_of_isotropic (U : WeightedCenteredH1 φ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hV : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ))
    (hU : ‖weightedH1Value φ U‖ = 1) {lam : ℝ}
    (heigen : ∀ x, weightedDiffusion φ f x = -lam * f x)
    (hiso : IsIsotropic (potentialMeasure φ)) :
    weightedIterationMeanLoss hφ hκ hlower (weightedSingleFamily U) 0 ≤ lam ^ 2 :=
  weightedEigenIteration_initial_meanLoss_le hφ hκ hlower U hf hV hU heigen
    (fun v => by simpa only [real_inner_comm v] using (hiso.integral_inner_sq v).le)

end KLS
end
#print axioms KLS.eigen_mean_gradient_sq_le
#print axioms KLS.weightedEigenIteration_initial_meanLoss_le
#print axioms KLS.weightedEigenIteration_initial_meanLoss_le_of_isotropic
