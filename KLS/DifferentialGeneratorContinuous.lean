import KLS.AdaptiveGlobalEnergyIto

/-! Continuity of the genuine generator with continuous coefficients. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}

theorem continuous_differentialGenerator {f : E → F} {b : E → E} {σ : Fin q → E → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : Continuous b) (hσ : ∀ k, Continuous (σ k)) :
    Continuous (fun x => differentialGenerator (b x) (fun k => σ k x) f x) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2d : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by simp)
  have h2 := h2d.continuous
  have he (x : E) (k : Fin q) :
      fderiv ℝ (fun y => fderiv ℝ f y (σ k x)) x (σ k x) =
        fderiv ℝ (fderiv ℝ f) x (σ k x) (σ k x) := by
    rw [fderiv_clm_apply (h1.differentiable (by simp) x) (differentiableAt_const _)]
    simp
  simp only [differentialGenerator, he]
  exact (h1.continuous.clm_apply hb).add
    ((continuous_finsetSum _ fun k _ => (h2.clm_apply (hσ k)).clm_apply (hσ k)).const_smul _)

end KLS.TensorEnergy
end
