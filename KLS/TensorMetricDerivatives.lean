import KLS.CoordinateQuadraticDerivatives
import KLS.TensorMetricSmooth

/-! Actual first and second derivatives of the tensor metric at identity.
The nonlinear-field curvature terms are retained for generator composition. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem differentiableAt_directional_of_contDiff {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x v : E) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
  (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)) x).clm_apply
    (differentiableAt_const v)

theorem fderiv_tensorMetric_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ} {x : E}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : DifferentiableAt ℝ T x) (hI : A x = 1) (v : E) :
    fderiv ℝ (fun y => tensorMetric (A y) (T y)) x v =
      2 * (T x ⬝ᵥ fderiv ℝ T x v) -
        T x ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) := by
  have hQ := (contDiff_tensorInverse (r := r) hA hdet).differentiable (by simp) x
  unfold tensorMetric
  rw [fderiv_quadratic_at_identity hQ hT (by simp [hI, tensorMatrix_one]) v,
    fderiv_tensorInverse_at_identity (hA.differentiable (by simp) x) hI v]
  simp [Matrix.neg_mulVec, sub_eq_add_neg]

theorem fderiv_fderiv_tensorMetric_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ} {x : E}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hI : A x = 1) (v : E)
    (hH : (fderiv ℝ A x v).transpose = fderiv ℝ A x v) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMetric (A z) (T z)) y v) x v =
      2 * (T x ⬝ᵥ fderiv ℝ (fun y => fderiv ℝ T y v) x v) -
      T x ⬝ᵥ (tensorSlotSum (fderiv ℝ (fun y => fderiv ℝ A y v) x v) *ᵥ T x) +
      2 * (fderiv ℝ T x v ⬝ᵥ fderiv ℝ T x v) -
      4 * (fderiv ℝ T x v ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x)) +
      (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) +
      ∑ s, (tensorSlot s (fderiv ℝ A x v) *ᵥ T x) ⬝ᵥ (tensorSlot s (fderiv ℝ A x v) *ᵥ T x) := by
  have hQ := contDiff_tensorInverse (r := r) hA hdet
  have hAd := hA.differentiable (by simp)
  have hAv := differentiableAt_directional_of_contDiff hA x v
  have hQv := differentiableAt_directional_of_contDiff hQ x v
  have hTv := differentiableAt_directional_of_contDiff hT x v
  have hQI : tensorMatrix (r := r) (A x)⁻¹ = 1 := by simp [hI, tensorMatrix_one]
  have hQS : (fderiv ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x v).transpose =
      fderiv ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x v := by
    rw [fderiv_tensorInverse_at_identity (hAd x) hI v]
    simp only [Matrix.transpose_neg, tensorSlotSum_transpose, hH]
  unfold tensorMetric
  rw [fderiv_fderiv_quadratic_at_identity (hQ.differentiable (by simp))
    (hT.differentiable (by simp)) v hQv hTv hQI hQS,
    fderiv_tensorInverse_at_identity (hAd x) hI v,
    fderiv_fderiv_tensorInverse_at_identity hAd hdet v hAv hI]
  simp only [Matrix.neg_mulVec, dotProduct_neg, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_add, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum]
  rw [dotProduct_matrix_square _ (by rw [tensorSlotSum_transpose, hH])]
  have hs (s : Fin r) := dotProduct_matrix_square (tensorSlot s (fderiv ℝ A x v))
    (by rw [tensorSlot_transpose, hH]) (T x)
  simp_rw [hs]
  ring

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_fderiv_tensorMetric_at_identity
