import KLS.MollifiedTranslatedAverage

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A genuine smooth lower comparator at a maximum controls its log-density.
Only the comparator, not the weak moment potential, is assumed smooth. -/
theorem weak_moment_smooth_comparison_at_max
    {u V g : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hg : ContDiff ℝ 2 g) {α : ℝ} (hα : 0 < α) (x : Space n)
    (hmax : ∀ y, g y - α * u y ≤ g x - α * u x)
    (hpos : (coordinateHessian g x).PosDef) {b : ℝ}
    (hb : Real.exp b ≤ (coordinateHessian g x).det) :
    b ≤ -u x + V (gradient u x) + n * Real.log α := by
  let ψ := fun y => α⁻¹ * g y + (u x - α⁻¹ * g x)
  have hψ : ContDiff ℝ 2 ψ := (contDiff_const.mul hg).add contDiff_const
  have hψH : coordinateHessian ψ x = α⁻¹ • coordinateHessian g x := by
    rw [coordinateHessian_add_const]
    ext i j
    exact coordinateHessian_smul hg α⁻¹ x i j
  have hψpos : (coordinateHessian ψ x).PosDef := by
    rw [hψH]
    exact hpos.smul (inv_pos.mpr hα)
  have hcontact : u x = ψ x := by dsimp [ψ]; ring
  have htouch : ∀ᶠ y in 𝓝 x, ψ y ≤ u y := by
    apply Eventually.of_forall
    intro y
    have hh := mul_le_mul_of_nonneg_left (hmax y) (inv_pos.mpr hα).le
    have hi : α⁻¹ * α = 1 := inv_mul_cancel₀ hα.ne'
    simp only [mul_sub,← mul_assoc,hi,one_mul] at hh
    dsimp [ψ]
    linarith
  have hdet := moment_det_le_density_of_c2_semidefinite_lower_touch
    hLip hc hV hK hKc hpush hψ.contDiffAt hψpos.posSemidef hcontact htouch
  have hlo := Real.log_le_log hψpos.det_pos hdet
  rw [Real.log_exp,hψH,Matrix.det_smul,Fintype.card_fin,
    Real.log_mul (pow_ne_zero n (inv_ne_zero hα.ne')) hpos.det_pos.ne',
    Real.log_pow,Real.log_inv] at hlo
  have hblog := Real.log_le_log (Real.exp_pos b) hb
  rw [Real.log_exp] at hblog
  linarith

end KLS
end
