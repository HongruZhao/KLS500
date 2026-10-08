import SpectralReductionMovingJumpSumRecurrence
import SpectralReductionLongSumRecurrence
import SpectralReductionMeanSumRecurrence
import SpectralReductionGeneralStopping
import SpectralReductionGeneralMeanLoss
import KLS.WeightedIterationMeanLossBound
import KLS.WeightedEigenIterationSymmetrization
import SpectralReductionCoupledScalar
import SpectralReductionMoving256Taylor
import SpectralReductionRetainedStopping
import SpectralReductionCoupledStopping
import SpectralReductionRetainedJumpSum
import SpectralReductionRetainedMovingJumpSum
import SpectralReductionGeneralSymmetrization
import KLS.ThirdCumulant

/-! Reduced regular spectral criterion for the same faithful Poincare constant.
The scalar coordinate-Taylor norm bound remains an explicit premise. All
iteration, eigenvalue, defect, stopping, and mean-loss inputs are derived. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ}

/-- An actual coordinate-Taylor bound controls the faithful optimal
Poincare constant of a smooth uniformly convex probability potential. -/
theorem poincareConstant_le_of_coupledRankYoungTaylorBound
    {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hsecond : ∀ v : Space n,
      (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2)
    (hTaylor : WeightedCoordinateTaylorCoefficientBound φ moving256RankTaylorCoefficient) :
    poincareConstant (potentialMeasure φ) ≤
      ENNReal.ofReal (500 : ℝ) := by
  obtain ⟨lam,U,F,W,hlam,hU,hCP,hb,hF,hV,hL,heigen,hW,hE0,hD0,hB⟩ :=
    exists_attained_eigenvalue_retained_iteration hφ hκ hlower hn
  obtain ⟨N,ρ,hN,hρ,hρ1,hscale,hCeq,hcross⟩ :=
    weightedIteration_exists_coupled_defect_index hφ hκ hlower (weightedSingleFamily U) F W hF hV hL
      hlam (by norm_num : (1:ℝ)<1007/1000) (δ:=(1/100000)) (by norm_num) (by norm_num) hE0 hD0 hB
  let S : ℕ → ℝ :=
    weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N
  have hzero : ∀ d, N ≤ d → S d = 0 := by
    intro d hd
    exact weightedIterationTaylorSum_eq_zero (hφ.of_le (by simp)) hκ hlower
      (weightedSingleFamily U) N d hd
  have hS : ∀ d, 0 ≤ S d := fun d => weightedIterationTaylorSum_nonneg
    (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N d
  have hrec : ∀ d, 1 ≤ d → S d ≤ coupledRankMainCoefficient (1007 / 1000) d * lam ^ (coupledRankJump d) * S (d+coupledRankJump d) +
      coupledRankErrorCoefficient ρ (1007 / 1000) d * lam * moving256RankTaylorCoefficient d := by
    intro d hd
    have hh := weightedIteration_taylor_sum_recurrence_rankMovingJumpYoung_retained hφ hκ hlower (weightedSingleFamily U)
      F W hF hV hL hW (coupledYoungParameter_pos d) hlam (by norm_num : (1:ℝ)≤1007/1000)
      hb hTaylor moving256RankTaylorCoefficient_nonneg hE0 N hCeq.le hscale
      d (coupledRankJump d) (coupledRankWindow d) hd (coupledRankJump_pos hd) (coupledRankWindow_admissible d)
    simpa only [S,coupledRankMainCoefficient,coupledRankErrorCoefficient,coupledRankWeight,
      coupledRecoverySquared,jumpTaylorMainCoefficient,movingJumpTaylorErrorCoefficient,mul_assoc] using hh
  have hmeanLe := weightedIteration_sum_meanLoss_le_generalScale hφ hκ hlower U F hF hV hL
    hU heigen hsecond (N - 1) (fun k hk => hscale k (by omega))
  have hmean : (1-1/(1007/1000)-(1/100000)+ρ/(1007/1000))*lam < lam ^ 2 + (1007 / 1000) * lam * S 1 := by
    apply hcross.trans_le
    simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega), S,
      weightedIterationTaylorSum, weightedIterationTaylorEnergy] using hmeanLe
  have hgap := coupled_spectral_scalar_lower_bound hlam hρ hρ1 S hS N hzero hrec hmean
  have hprod : 1 < 500 * lam := by
    linarith
  have hinv : lam⁻¹ ≤ 500 := by
    rw [← one_div]
    apply (div_le_iff₀ hlam).2
    nlinarith
  rw [hCP]
  exact ENNReal.ofReal_le_ofReal hinv

/-- The actual regular isotropic strongly convex class satisfies the
rank-sensitive criterion without an additional Taylor or cumulant premise. -/
theorem poincareConstant_le_regular_coupledRankYoung
    {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn Set.univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal 500 := by
  have hlower := coordinateHessian_lower_of_strongConvexOn (hφ.of_le (by simp)) hstrong
  have hTaylor := weightedCoordinateTaylorCoefficientBound_moving256Rank (hφ.of_le (by simp)) hκ hstrong hiso
  apply poincareConstant_le_of_coupledRankYoungTaylorBound hn hφ hκ hlower (fun v => ?_) hTaylor
  simpa only [real_inner_comm v] using (hiso.integral_inner_sq v).le

end KLS.ConstantReduction
end

