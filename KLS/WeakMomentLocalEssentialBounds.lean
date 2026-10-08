import KLS.RawTraceLocalLp
import KLS.WeakMomentLipschitzInverseTests

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A continuous real function is essentially bounded on each compact set. -/
theorem memLp_continuous_top_on_compact
    {f : Space n → ℝ} (hf : Continuous f) {S : Set (Space n)} (hS : IsCompact S) :
    MemLp f ∞ (volume.restrict S) := by
  obtain ⟨C,hC⟩ := hS.bddAbove_image hf.norm.continuousOn
  apply memLp_top_of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC (mem_image_of_mem _ hx)

/-- Every actual Hessian entry of a Lipschitz gradient is bounded globally. -/
theorem memLp_coordinateHessian_top_of_gradient_lipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (μ : Measure (Space n)) (i j : Fin n) :
    MemLp (fun x => coordinateHessian u x i j) ∞ μ := by
  exact memLp_top_of_bound
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_coordinateHessian u))).aestronglyMeasurable) G
    (Eventually.of_forall fun x => coordinateHessian_entry_bound_of_gradient_lipschitz hG x i j)

/-- The actual adjugate entries share a global essential bound. -/
theorem memLp_adjugateHessian_top_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (μ : Measure (Space n)) (i j : Fin n) :
    MemLp (fun x => (coordinateHessian u x).adjugate i j) ∞ μ := by
  obtain ⟨C,hC,hbound,_⟩ := exists_uniform_adjugate_bound_of_gradient_lipschitz hLip hG
  have hm : Measurable (fun x : Space n => (coordinateHessian u x).adjugate) :=
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
      MatrixCalculus.contDiff_adjugate.continuous).measurable.comp (measurable_coordinateHessian u)
  exact memLp_top_of_bound
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).aestronglyMeasurable) C
    (Eventually.of_forall fun x => (Matrix.norm_le_iff hC).mp (hbound x) i j)

/-- The actual a.e. Monge-Ampere equation gives compact essential inverse
 bounds without assuming continuity of the source Hessian. -/
theorem memLp_inverseHessian_top_on_compact_of_ae_equation
    {u V : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hV : Continuous V)
    (hAe : ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian u x).PosDef ∧
      (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    {S : Set (Space n)} (hS : IsCompact S) (i j : Fin n) :
    MemLp (fun x => (coordinateHessian u x)⁻¹ i j) ∞ (volume.restrict S) := by
  have hcoef := memLp_continuous_top_on_compact
    (Real.continuous_exp.comp (hLip.continuous.sub (hV.comp hG.continuous))) hS
  have hadj := memLp_adjugateHessian_top_of_gradient_lipschitz hLip hG (volume.restrict S) i j
  apply MemLp.ae_eq (hf_Lp := hcoef.mul hadj)
  filter_upwards [ae_restrict_of_ae hAe] with x hx
  have he := exp_neg_target_mul_adjugate_eq_exp_neg_source_mul_inverse hx.1 hx.2 i j
  calc
    Real.exp (u x - V (gradient u x)) * (coordinateHessian u x).adjugate i j =
        Real.exp (u x) * (Real.exp (-V (gradient u x)) * (coordinateHessian u x).adjugate i j) := by
      rw [← mul_assoc, ← Real.exp_add, sub_eq_add_neg]
    _ = Real.exp (u x) * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j) := by rw [he]
    _ = (coordinateHessian u x)⁻¹ i j := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

end KLS
end
