import KLS.WeightedEnergyTail
import KLS.WeightedCompactL2Maps

/-! Actual square-cutoff operators approximate the weighted energy inclusion. -/
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

lemma smoothCutoff_eq_one_of_norm_le (k : ℕ) {x : Space n}
    (hx : ‖x‖ ≤ (k : ℝ) + 1) : smoothCutoff n k x = 1 := by
  apply (unitCutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (cutoffScale_pos k)]
  change cutoffScale k * ‖x‖ ≤ 1
  calc
    _ ≤ cutoffScale k * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hx (cutoffScale_pos k).le
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- Returning a compact localization to the weighted space multiplies by the square
of the actual cutoff, and its error is bounded by the actual exterior mass. -/
theorem weightedL2_square_cutoff_error_sq_le {φ χ : Space n → ℝ} {R : ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hone : ∀ x, ‖x‖ ≤ R → χ x = 1)
    (u : Lp ℝ 2 (potentialMeasure φ)) :
    ‖u - volumeL2CompactToWeighted hφ hχ hc (weightedL2CompactToVolume hφ hχ hc u)‖ ^ 2 ≤
      ∫ x in {x | R ≤ ‖x‖}, u x ^ 2 ∂potentialMeasure φ := by
  let v := volumeL2CompactToWeighted hφ hχ hc (weightedL2CompactToVolume hφ hχ hc u)
  have hv := volumeL2CompactToWeighted_comp_coe hφ hχ hc u
  have hsub : u - v =ᵐ[potentialMeasure φ] fun x => (1 - χ x ^ 2) * u x := by
    filter_upwards [Lp.coeFn_sub u v, hv] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    ring
  have hs : MeasurableSet {x : Space n | R ≤ ‖x‖} :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hs]
  apply integral_mono_ae
  · exact L2.integrable_inner (u - v) (u - v)
  · exact (Lp.memLp u).integrable_sq.indicator hs
  · filter_upwards [hsub] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases hRx : R ≤ ‖x‖
    · rw [Set.indicator_of_mem (show x ∈ {x | R ≤ ‖x‖} from hRx)]
      have hχ := hb x
      have hχ2 : 0 ≤ χ x ^ 2 ∧ χ x ^ 2 ≤ 1 := ⟨sq_nonneg _, by nlinarith⟩
      have he : (1 - χ x ^ 2) ^ 2 ≤ 1 := by nlinarith [hχ2.1, hχ2.2]
      have ht := mul_le_mul_of_nonneg_right he (sq_nonneg (u x))
      nlinarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | R ≤ ‖x‖} from hRx),
        hone x (not_le.mp hRx).le]
      simp

def weightedH1SquareCutoff {φ : Space n → ℝ} (hφ : Continuous φ) (k : ℕ) :
    WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (volumeL2CompactToWeighted hφ (smoothCutoff_contDiff k).continuous
    (smoothCutoff_hasCompactSupport k)).comp
    (weightedH1CompactValue hφ (smoothCutoff_contDiff k).continuous
      (smoothCutoff_hasCompactSupport k))

theorem weightedH1SquareCutoff_error_sq_le {φ : Space n → ℝ}
    (hφ : Continuous φ) (k : ℕ) (U : WeightedCenteredH1 φ) :
    ‖weightedH1Value φ U - weightedH1SquareCutoff hφ k U‖ ^ 2 ≤
      ∫ x in {x | (k : ℝ) + 1 ≤ ‖x‖}, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ :=
  weightedL2_square_cutoff_error_sq_le hφ (smoothCutoff_contDiff k).continuous
    (smoothCutoff_hasCompactSupport k) (smoothCutoff_nonneg_le_one k)
    (fun _ hx => smoothCutoff_eq_one_of_norm_le k hx) (weightedH1Value φ U)

/-- A derived finite constant gives an operator-norm error tending to zero. -/
theorem exists_weightedH1SquareCutoff_opNorm_bound {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) :
    ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ,
      ‖weightedH1Value φ - weightedH1SquareCutoff hφ.continuous k‖ ≤ B * cutoffScale k := by
  obtain ⟨C, hC, hb⟩ := exists_weightedH1_tail_bound hφ hκ hlower
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro k
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg C) (cutoffScale_pos k).le)
  intro U
  have h := (weightedH1SquareCutoff_error_sq_le hφ.continuous k U).trans
    (hb ((k : ℝ) + 1) (by positivity) U)
  have he : ((Real.sqrt C * cutoffScale k) * ‖U‖) ^ 2 =
      C / ((k : ℝ) + 1) ^ 2 * ‖U‖ ^ 2 := by
    dsimp [cutoffScale]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le]
    field_simp
  change ‖weightedH1Value φ U - weightedH1SquareCutoff hφ.continuous k U‖ ≤ _
  have hn : 0 ≤ (Real.sqrt C * cutoffScale k) * ‖U‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) (cutoffScale_pos k).le) (norm_nonneg U)
  nlinarith [norm_nonneg (weightedH1Value φ U - weightedH1SquareCutoff hφ.continuous k U)]

theorem weightedH1SquareCutoff_tendsto {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) :
    Tendsto (weightedH1SquareCutoff hφ.continuous) atTop (𝓝 (weightedH1Value φ)) := by
  obtain ⟨B, hB, hb⟩ := exists_weightedH1SquareCutoff_opNorm_bound hφ hκ hlower
  apply (tendsto_iff_norm_sub_tendsto_zero
    (E := WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ))
    (f := weightedH1SquareCutoff hφ.continuous) (a := atTop) (b := weightedH1Value φ)).mpr
  have ht : Tendsto (fun k => B * cutoffScale k) atTop (𝓝 0) := by
    simpa using cutoffScale_tendsto_zero.const_mul B
  exact squeeze_zero
    (fun k => norm_nonneg (weightedH1SquareCutoff hφ.continuous k - weightedH1Value φ))
    (fun k => (norm_sub_rev (weightedH1SquareCutoff hφ.continuous k)
      (weightedH1Value φ)).le.trans (hb k)) ht

end KLS
end
#print axioms KLS.weightedL2_square_cutoff_error_sq_le
#print axioms KLS.exists_weightedH1SquareCutoff_opNorm_bound
#print axioms KLS.weightedH1SquareCutoff_tendsto
