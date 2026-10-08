import KLS.AdaptiveEnergyExpectation

/-! The genuine first derivative of the tensor energy in fixed whitening
coordinates. The whitening matrix is kept fixed while differentiating. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_tensorMetric_whitened
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (x v : E)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPs : P.transpose = P) (hP : P.det ≠ 0)
    (hwhite : P*A x*P = 1) :
    fderiv ℝ (fun y => tensorMetric (A y) (T y)) x v =
      2 * ((tensorMatrix P *ᵥ T x) ⬝ᵥ (tensorMatrix P *ᵥ fderiv ℝ T x v)) -
      (tensorMatrix P *ᵥ T x) ⬝ᵥ
        (tensorSlotSum (P * fderiv ℝ A x v * P) *ᵥ (tensorMatrix P *ᵥ T x)) := by
  let A' : E → Matrix (Fin n) (Fin n) ℝ := fun y => matrixCongruenceCLM P (A y)
  let T' : E → (Fin r → Fin n) → ℝ := fun y => tensorTransformCLM P (T y)
  have hA' : ContDiff ℝ (⊤ : ℕ∞) A' := (matrixCongruenceCLM P).contDiff.comp hA
  have hT' : ContDiff ℝ (⊤ : ℕ∞) T' := (tensorTransformCLM P).contDiff.comp hT
  have hdet' : ∀ y, (A' y).det ≠ 0 := by
    intro y
    change (P*A y*P).det ≠ 0
    simp only [Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hP (hdet y)) hP
  have hfdA : fderiv ℝ A' x v = P*fderiv ℝ A x v*P :=
    fderiv_compCLM_apply (matrixCongruenceCLM P) (hA.differentiable (by simp) x) v
  have hfdT : fderiv ℝ T' x v = tensorMatrix P *ᵥ fderiv ℝ T x v :=
    fderiv_compCLM_apply (tensorTransformCLM P) (hT.differentiable (by simp) x) v
  have hF : (fun y => tensorMetric (A' y) (T' y)) = fun y => tensorMetric (A y) (T y) := by
    funext y
    exact tensorMetric_congruence (A y) P hPs hP (T y)
  have hh := fderiv_tensorMetric_at_identity hA' hdet'
    (hT'.differentiable (by simp) x) hwhite v
  rw [hF, hfdA, hfdT] at hh
  exact hh

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_tensorMetric_whitened
