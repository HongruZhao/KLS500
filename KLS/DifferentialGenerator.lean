import KLS.TensorMetricDerivatives

/-! A finite-dimensional differential generator defined directly by actual
Fréchet derivatives, and its behavior under fixed continuous linear maps. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {q : ℕ}

/-- The coefficients are frozen at the evaluation point. -/
def differentialGenerator (b : E) (σ : Fin q → E) (f : E → F) (x : E) : F :=
  fderiv ℝ f x b + (1/2 : ℝ) • ∑ k, fderiv ℝ (fun y => fderiv ℝ f y (σ k)) x (σ k)

theorem fderiv_compCLM_apply (L : F →L[ℝ] G) {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y => L (f y)) x v = L (fderiv ℝ f x v) := by
  have h : HasFDerivAt (fun y => L (f y)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fderiv_fderiv_compCLM_apply (L : F →L[ℝ] G) {f : E → F} {x : E}
    (hf : Differentiable ℝ f) (v w : E)
    (hfv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => L (f z)) y v) x w =
      L (fderiv ℝ (fun y => fderiv ℝ f y v) x w) := by
  have heq : (fun y => fderiv ℝ (fun z => L (f z)) y v) =
      fun y => L (fderiv ℝ f y v) := by
    funext y
    exact fderiv_compCLM_apply L (hf y) v
  rw [heq, fderiv_compCLM_apply L hfv w]

theorem differentialGenerator_compCLM (L : F →L[ℝ] G) {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (b : E) (σ : Fin q → E) (x : E) :
    differentialGenerator b σ (fun y => L (f y)) x =
      L (differentialGenerator b σ f x) := by
  unfold differentialGenerator
  rw [fderiv_compCLM_apply L (hf.differentiable (by simp) x) b]
  simp_rw [fderiv_fderiv_compCLM_apply L (hf.differentiable (by simp)) _ _
    (differentiableAt_directional_of_contDiff hf x _)]
  simp only [map_add, map_smul, map_sum]

variable {n r : ℕ}

theorem tensorSlotSum_smul (c : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlotSum (r := r) (c • H) = c • tensorSlotSum H := by
  simp [tensorSlotSum, tensorSlot_smul, Finset.smul_sum]

def tensorSlotSumCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := tensorSlotSum
    map_add' := tensorSlotSum_add
    map_smul' := tensorSlotSum_smul }

theorem tensorSlotSumCLM_apply (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlotSumCLM (r := r) H = tensorSlotSum H := rfl

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.differentialGenerator_compCLM
