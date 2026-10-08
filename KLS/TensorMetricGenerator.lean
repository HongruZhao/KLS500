import KLS.DifferentialGenerator

/-! Exact energy-generator identity, with no stochastic or universal tensor
estimate hidden in the hypotheses. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differentialGenerator_tensorMetric_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (b : E) (σ : Fin q → E) (x : E)
    (hI : A x = 1) (hH : ∀ k, (fderiv ℝ A x (σ k)).transpose = fderiv ℝ A x (σ k)) :
    differentialGenerator b σ (fun y => tensorMetric (A y) (T y)) x =
      2 * (T x ⬝ᵥ differentialGenerator b σ T x) -
      T x ⬝ᵥ (tensorSlotSum (differentialGenerator b σ A x) *ᵥ T x) +
      ∑ k, (fderiv ℝ T x (σ k) ⬝ᵥ fderiv ℝ T x (σ k) -
        2 * (fderiv ℝ T x (σ k) ⬝ᵥ (tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x)) +
        (1/2 : ℝ) * ((tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x)) +
        (1/2 : ℝ) * ∑ s, ((tensorSlot s (fderiv ℝ A x (σ k)) *ᵥ T x) ⬝ᵥ
          (tensorSlot s (fderiv ℝ A x (σ k)) *ᵥ T x))) := by
  unfold differentialGenerator
  rw [fderiv_tensorMetric_at_identity hA hdet (hT.differentiable (by simp) x) hI b]
  simp_rw [fderiv_fderiv_tensorMetric_at_identity hA hdet hT hI _ (hH _)]
  rw [tensorSlotSum_add, tensorSlotSum_smul]
  have hSum (M : Fin q → Matrix (Fin n) (Fin n) ℝ) :
      tensorSlotSum (r := r) (∑ k, M k) = ∑ k, tensorSlotSum (M k) :=
    map_sum (tensorSlotSumCLM (r := r)) M Finset.univ
  rw [hSum]
  simp only [smul_eq_mul, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The drift part of paper (89) follows from the actual matrix and tensor
field generators, before any lower bound on the noise terms. -/
theorem differentialGenerator_tensorMetric_with_drift
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (b : E) (σ : Fin q → E) (x : E)
    (hI : A x = 1) (hH : ∀ k, (fderiv ℝ A x (σ k)).transpose = fderiv ℝ A x (σ k))
    (m : ℝ) (L : (Fin r → Fin n) → ℝ)
    (hGA : differentialGenerator b σ A x = -1)
    (hGT : differentialGenerator b σ T x = -(m • T x + L)) :
    differentialGenerator b σ (fun y => tensorMetric (A y) (T y)) x =
      (r - 2*m) * (T x ⬝ᵥ T x) - 2 * (T x ⬝ᵥ L) +
      ∑ k, (fderiv ℝ T x (σ k) ⬝ᵥ fderiv ℝ T x (σ k) -
        2 * (fderiv ℝ T x (σ k) ⬝ᵥ (tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x)) +
        (1/2 : ℝ) * ((tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ A x (σ k)) *ᵥ T x)) +
        (1/2 : ℝ) * ∑ s, ((tensorSlot s (fderiv ℝ A x (σ k)) *ᵥ T x) ⬝ᵥ
          (tensorSlot s (fderiv ℝ A x (σ k)) *ᵥ T x))) := by
  rw [differentialGenerator_tensorMetric_at_identity hA hdet hT b σ x hI hH, hGA, hGT,
    tensorSlotSum_neg, tensorSlotSum_one]
  simp only [dotProduct_neg, dotProduct_add, dotProduct_smul, Matrix.neg_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  ring

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.differentialGenerator_tensorMetric_at_identity
#print axioms KLS.TensorEnergy.differentialGenerator_tensorMetric_with_drift
