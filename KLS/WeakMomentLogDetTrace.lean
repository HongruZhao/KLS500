import KLS.MomentFullViscosity
import KLS.MatrixLogDetTangent

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Log determinant is the infimum of its genuine linear trace majorants. -/
theorem le_log_det_iff_forall_posDef_trace
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (b : ℝ) :
    b ≤ Real.log H.det ↔ ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef →
      b + Real.log J.det + n ≤ (J * H).trace := by
  constructor
  · intro hb J hJ
    have hh := log_det_tangent_bound hJ.inv hH
    rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ.det_pos.ne'),
      Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv] at hh
    linarith
  · intro h
    have hh := h H⁻¹ hH.inv
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.trace_one,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv] at hh
    simp only [Fintype.card_fin] at hh
    linarith

/-- Every upper touching test of the actual weak moment potential satisfies
all constant-coefficient trace inequalities. No source Hessian or gradient
Lipschitz bound is a hypothesis. -/
theorem weak_moment_upper_test_trace_bound
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x : Space n} (hψ : ContDiffAt ℝ 2 ψ x)
    (hcontact : u x = ψ x) (htouch : ∀ᶠ y in 𝓝 x, u y ≤ ψ y)
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    -u x + V (gradient u x) + Real.log J.det + n ≤ (J * coordinateHessian ψ x).trace := by
  have hH := moment_c2_upper_test_hessian_posDef hLip hc hV hK hKc hpush hψ hcontact htouch
  have hd := moment_det_ge_density_of_any_c2_upper_touch hLip hc hV hK hKc hpush
    hψ hcontact htouch
  have hl := Real.log_le_log (Real.exp_pos _) hd
  rw [Real.log_exp] at hl
  exact (le_log_det_iff_forall_posDef_trace hH _).mp hl J hJ

end KLS
end
