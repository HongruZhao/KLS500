import KLS.TensorEnergyCorrection

/-! Fixed congruence transports the actual differential generator to identity.
Every transformation is an explicit continuous linear map. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def matrixCongruenceCLM (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => P*M*P
    map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }

def tensorTransformCLM (P : Matrix (Fin n) (Fin n) ℝ) :
    ((Fin r → Fin n) → ℝ) →L[ℝ] ((Fin r → Fin n) → ℝ) :=
  (tensorMatrix P).mulVecLin.toContinuousLinearMap

theorem matrixCongruenceCLM_apply (P A : Matrix (Fin n) (Fin n) ℝ) :
    matrixCongruenceCLM P A = P*A*P := rfl

theorem tensorTransformCLM_apply (P : Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ) : tensorTransformCLM P T = tensorMatrix P *ᵥ T := rfl

/-- Paper (86)--(89), for a fixed actual whitening matrix. The hypotheses on
matrix and tensor drift are values of genuine differential generators. -/
theorem differentialGenerator_tensorMetric_whitened
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (b : E) (σ : Fin q → E) (x : E)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPs : P.transpose = P) (hP : P.det ≠ 0)
    (hwhite : P*A x*P = 1)
    (hH : ∀ k, (fderiv ℝ A x (σ k)).transpose = fderiv ℝ A x (σ k))
    (m : ℝ) (L : (Fin r → Fin n) → ℝ)
    (hGA : differentialGenerator b σ A x = -A x)
    (hGT : differentialGenerator b σ T x = -(m • T x + L)) :
    differentialGenerator b σ (fun y => tensorMetric (A y) (T y)) x =
      (r - 2*m) * ((tensorMatrix P *ᵥ T x) ⬝ᵥ (tensorMatrix P *ᵥ T x)) -
      2 * ((tensorMatrix P *ᵥ T x) ⬝ᵥ (tensorMatrix P *ᵥ L)) +
      ∑ k, energyNoiseCorrection (tensorMatrix P *ᵥ T x)
        (P * fderiv ℝ A x (σ k) * P) (tensorMatrix P *ᵥ fderiv ℝ T x (σ k)) := by
  let A' : E → Matrix (Fin n) (Fin n) ℝ := fun y => matrixCongruenceCLM P (A y)
  let T' : E → (Fin r → Fin n) → ℝ := fun y => tensorTransformCLM P (T y)
  have hA' : ContDiff ℝ (⊤ : ℕ∞) A' := (matrixCongruenceCLM P).contDiff.comp hA
  have hT' : ContDiff ℝ (⊤ : ℕ∞) T' := (tensorTransformCLM P).contDiff.comp hT
  have hdet' : ∀ y, (A' y).det ≠ 0 := by
    intro y
    change (P*A y*P).det ≠ 0
    simp only [Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hP (hdet y)) hP
  have hI' : A' x = 1 := hwhite
  have hfdA (v : E) : fderiv ℝ A' x v = P*fderiv ℝ A x v*P :=
    fderiv_compCLM_apply (matrixCongruenceCLM P) (hA.differentiable (by simp) x) v
  have hfdT (v : E) : fderiv ℝ T' x v = tensorMatrix P *ᵥ fderiv ℝ T x v :=
    fderiv_compCLM_apply (tensorTransformCLM P) (hT.differentiable (by simp) x) v
  have hH' : ∀ k, (fderiv ℝ A' x (σ k)).transpose = fderiv ℝ A' x (σ k) := by
    intro k
    rw [hfdA]
    simp [Matrix.transpose_mul, hPs, hH k, Matrix.mul_assoc]
  have hGA' : differentialGenerator b σ A' x = -1 := by
    rw [show A' = fun y => matrixCongruenceCLM P (A y) from rfl,
      differentialGenerator_compCLM (matrixCongruenceCLM P) hA, hGA]
    simp only [map_neg, matrixCongruenceCLM_apply, hwhite]
  have hGT' : differentialGenerator b σ T' x = -(m • T' x + tensorMatrix P *ᵥ L) := by
    rw [show T' = fun y => tensorTransformCLM P (T y) from rfl,
      differentialGenerator_compCLM (tensorTransformCLM P) hT, hGT]
    simp only [map_neg, map_add, map_smul, tensorTransformCLM_apply]
  have hF : (fun y => tensorMetric (A' y) (T' y)) = fun y => tensorMetric (A y) (T y) := by
    funext y
    exact tensorMetric_congruence (A y) P hPs hP (T y)
  have hh := differentialGenerator_tensorMetric_with_drift hA' hdet' hT' b σ x hI' hH'
    m (tensorMatrix P *ᵥ L) hGA' hGT'
  rw [hF] at hh
  simp_rw [hfdA, hfdT] at hh
  exact hh

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.differentialGenerator_tensorMetric_whitened
