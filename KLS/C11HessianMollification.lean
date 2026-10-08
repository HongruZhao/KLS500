import KLS.LipschitzDerivativeMollification
import KLS.BoundedWeightedMollification

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Each actual Hessian entry is globally bounded by the gradient Lipschitz
 constant, including the total-derivative values at exceptional points. -/
theorem coordinateHessian_entry_bound_of_gradient_lipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (x : Space n) (i j : Fin n) : ‖coordinateHessian u x i j‖ ≤ G := by
  have hcoord := lipschitz_coordinateDerivative_of_gradient_lipschitz hG j
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hcoord
  have hh := ((fderiv ℝ (coordinateDerivative u j) x).le_opNorm (EuclideanSpace.single i 1)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  simpa only [coordinateHessian,coordinateDerivative,PiLp.norm_single,norm_one,mul_one] using hh

/-- Actual Hessian entries of a C1,1 potential are locally integrable. -/
theorem locallyIntegrable_coordinateHessian_of_gradient_lipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    LocallyIntegrable (fun x => coordinateHessian u x i j) volume := by
  have hm : Measurable (fun x => coordinateHessian u x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_coordinateHessian u))
  exact (memLp_top_of_bound hm.aestronglyMeasurable G
    (Eventually.of_forall fun x => coordinateHessian_entry_bound_of_gradient_lipschitz hG x i j)).locallyIntegrable le_top

/-- Actual smooth Hessians converge entrywise almost everywhere to the actual
 iterated-derivative Hessian of a Lipschitz potential with Lipschitz gradient. -/
theorem coordinateHessian_mollify_tendsto_ae_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (mollify k u) x) atTop (𝓝 (coordinateHessian u x)) := by
  have hentry (i j : Fin n) : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (mollify k u) x i j) atTop (𝓝 (coordinateHessian u x i j)) := by
    simpa only [coordinateHessian_mollify_of_gradient_lipschitz hLip hG] using
      mollify_tendsto_ae (locallyIntegrable_coordinateHessian_of_gradient_lipschitz hG i j)
  have ha := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hentry i j))
  filter_upwards [ha] with x hx
  exact tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hx i j))

/-- The actual Hessian entries converge strongly in L2 for any finite measure
 absolutely continuous with respect to volume, in particular on each compact
 set. No globally square-integrable potential or Hessian is assumed. -/
theorem coordinateHessian_mollify_weighted_L2_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : μ ≪ volume) (i j : Fin n) :
    (∀ k, MemLp (fun x => coordinateHessian (mollify k u) x i j) 2 μ) ∧
      MemLp (fun x => coordinateHessian u x i j) 2 μ ∧
      Tendsto (fun k => eLpNorm
        ((fun x => coordinateHessian (mollify k u) x i j) - (fun x => coordinateHessian u x i j)) 2 μ)
        atTop (𝓝 0) := by
  have hh := bounded_mollify_weighted_L2_convergence hμ
    (locallyIntegrable_coordinateHessian_of_gradient_lipschitz hG i j) G.coe_nonneg
    (Eventually.of_forall fun x => coordinateHessian_entry_bound_of_gradient_lipschitz hG x i j)
  simpa only [coordinateHessian_mollify_of_gradient_lipschitz hLip hG] using hh

end KLS
end
