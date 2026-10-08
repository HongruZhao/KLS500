import KLS.C11HessianMollification

open MeasureTheory Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The genuine adjugates of the original and mollified Hessians share a
 finite global bound determined by the gradient Lipschitz constant. -/
theorem exists_uniform_adjugate_bound_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(coordinateHessian u x).adjugate‖ ≤ C) ∧
      ∀ k x, ‖(coordinateHessian (mollify k u) x).adjugate‖ ≤ C := by
  have hB := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) (G : ℝ)).bddAbove_image
    MatrixCalculus.contDiff_adjugate.continuous.norm.continuousOn
  obtain ⟨B,hB⟩ := hB
  have hbound (A : Matrix (Fin n) (Fin n) ℝ) (hA : ‖A‖ ≤ G) : ‖A.adjugate‖ ≤ max B 0 :=
    (hB (mem_image_of_mem _ (show A ∈ closedBall 0 (G : ℝ) by simpa using hA))).trans (le_max_left _ _)
  refine ⟨max B 0,le_max_right _ _,fun x => hbound _ ?_,fun k x => hbound _ ?_⟩
  · exact (Matrix.norm_le_iff G.coe_nonneg).mpr
      (fun i j => coordinateHessian_entry_bound_of_gradient_lipschitz hG x i j)
  · apply (Matrix.norm_le_iff G.coe_nonneg).mpr
    intro i j
    rw [coordinateHessian_mollify_of_gradient_lipschitz hLip hG]
    exact norm_mollify_le_of_ae_bound
      (Eventually.of_forall fun y => coordinateHessian_entry_bound_of_gradient_lipschitz hG y i j) k x

/-- Actual adjugate Hessian coefficients converge against every compact
 continuous test. The proof uses actual a.e. Hessian convergence and a genuine
 uniform bound, so no continuity of the original Hessian is required. -/
theorem tendsto_integral_adjugateHessian_mollify_mul
    {u ψ : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (i j : Fin n) :
    Tendsto (fun k => ∫ x, (coordinateHessian (mollify k u) x).adjugate i j * ψ x)
      atTop (𝓝 (∫ x, (coordinateHessian u x).adjugate i j * ψ x)) := by
  obtain ⟨C,hC,_,hbound⟩ := exists_uniform_adjugate_bound_of_gradient_lipschitz hLip hG
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun x => (coordinateHessian (mollify k u) x).adjugate i j * ψ x) volume := by
    have hm : Measurable (fun x : Space n => (coordinateHessian (mollify k u) x).adjugate) :=
      (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
        MatrixCalculus.contDiff_adjugate.continuous).measurable.comp (measurable_coordinateHessian (mollify k u))
    exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).mul hψ.measurable).aestronglyMeasurable
  have hdom (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖(coordinateHessian (mollify k u) x).adjugate i j * ψ x‖ ≤ C*‖ψ x‖ :=
    Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((Matrix.norm_le_iff hC).mp (hbound k x) i j) (norm_nonneg _)
  have hlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => (coordinateHessian (mollify k u) x).adjugate i j * ψ x) atTop
      (𝓝 ((coordinateHessian u x).adjugate i j * ψ x)) := by
    filter_upwards [coordinateHessian_mollify_tendsto_ae_of_gradient_lipschitz hLip hG] with x hx
    have ha := MatrixCalculus.contDiff_adjugate.continuous.continuousAt.tendsto.comp hx
    exact ((ha.apply_nhds i).apply_nhds j).mul_const (ψ x)
  exact tendsto_integral_of_dominated_convergence (fun x => C*‖ψ x‖) hmeas
    ((hψ.integrable_of_hasCompactSupport hc).norm.const_mul C) hdom hlim

end KLS
end
