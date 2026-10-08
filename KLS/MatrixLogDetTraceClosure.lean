import KLS.WeakMomentLogDetTrace
import KLS.ScalarMollification

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The full family of linear trace lower bounds forces strict positivity and
an actual determinant lower bound, even when only semidefiniteness was known. -/
theorem posDef_and_exp_le_det_of_forall_trace
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef) {b : ℝ}
    (htrace : ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef →
      b + Real.log J.det + n ≤ (J * H).trace) :
    H.PosDef ∧ Real.exp b ≤ H.det := by
  have hreg (ε : ℝ) (hε : 0 < ε) : Real.exp b ≤ (H + ε • 1).det := by
    have hpos : (H + ε • 1).PosDef := Matrix.PosDef.posSemidef_add hH (Matrix.PosDef.one.smul hε)
    have ht := htrace (H + ε • 1)⁻¹ hpos.inv
    have hprod : (H + ε • 1)⁻¹ * H = 1 - ε • (H + ε • 1)⁻¹ := by
      have hh := Matrix.nonsing_inv_mul (H + ε • 1)
        (isUnit_iff_ne_zero.mpr hpos.det_pos.ne')
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at hh
      exact eq_sub_of_add_eq hh
    rw [hprod, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul,
      Fintype.card_fin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv] at ht
    simp only [smul_eq_mul] at ht
    have hn := mul_nonneg hε.le hpos.inv.posSemidef.trace_nonneg
    have hl : b ≤ Real.log (H + ε • 1).det := by linarith
    exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log hpos.det_pos)
  have hlim : Tendsto (fun k => (H + cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ)).det)
      atTop (𝓝 H.det) := by
    have hh : Tendsto (fun k => H + cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ))
        atTop (𝓝 H) := by
      simpa using tendsto_const_nhds.add (cutoffScale_tendsto_zero.smul_const (1 : Matrix (Fin n) (Fin n) ℝ))
    exact Continuous.matrix_det continuous_id |>.continuousAt.tendsto.comp hh
  have hd := ge_of_tendsto hlim (Eventually.of_forall fun k => hreg _ (cutoffScale_pos k))
  exact ⟨hH.posDef_iff_det_ne_zero.mpr (lt_of_lt_of_le (Real.exp_pos b) hd).ne', hd⟩

end KLS
end
