import OptCollectivePolynomialEigenvalue
import OptSymmetricSpectralBound
import OptTensorDiagonalInjectivity

/-! Actual norm bound for the collective action on every symmetric tensor. -/
open Matrix Set WithLp
open scoped BigOperators Matrix.Norms.Elementwise RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

def symmetricCollectiveSquare (H : Fin q → Matrix (Fin n) (Fin n) ℝ) :
    symmetricTensorSubspace n r →ₗ[ℝ] symmetricTensorSubspace n r :=
  ∑ k, symmetricTensorSlot (r := r) (H k) ^ 2

theorem symmetricCollectiveSquare_isSymmetric
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ k, (H k).transpose = H k) :
    (symmetricCollectiveSquare (r := r) H).IsSymmetric := by
  exact LinearMap.isSymmetric_sum _ (fun k _ => (symmetricTensorSlot_isSymmetric (H k) (hH k)).pow 2)

theorem symmetricCollectiveSquare_coordinates
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (T : symmetricTensorSubspace n r) :
    (symmetricCollectiveSquare H T).val.ofLp =
      ∑ k, tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ T.val.ofLp) := by
  funext a
  simp only [symmetricCollectiveSquare, LinearMap.sum_apply, pow_two, Module.End.mul_apply,
    Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply, symmetricTensorSlot_apply]
  rfl

theorem norm_sq_eq_dotProduct {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖^2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

theorem symmetricCollectiveSquare_inner
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ k, (H k).transpose = H k)
    (T : symmetricTensorSubspace n r) :
    inner ℝ T (symmetricCollectiveSquare H T) =
      ∑ k, (tensorSlotSum (H k) *ᵥ T.val.ofLp) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T.val.ofLp) := by
  simp only [symmetricCollectiveSquare, LinearMap.sum_apply, inner_sum, pow_two, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← symmetricTensorSlot_isSymmetric (H k) (hH k) T (symmetricTensorSlot (H k) T)]
  change inner ℝ (symmetricTensorSlot (H k) T).val (symmetricTensorSlot (H k) T).val = _
  rw [real_inner_self_eq_norm_sq, norm_sq_eq_dotProduct]
  rfl

theorem symmetricCollectiveSquare_inner_le (hr : 2 ≤ r)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ k, (H k).transpose = H k)
    (K h : ℝ)
    (hK : ∀ x : Space n, ‖x‖ = 1 → ∑ k, ‖(H k).toEuclideanLin x‖^2 ≤ K)
    (hh : ∀ x : Space n, ‖x‖ = 1 → ∑ k, (inner ℝ x ((H k).toEuclideanLin x))^2 ≤ h)
    (T : symmetricTensorSubspace n r) :
    inner ℝ T (symmetricCollectiveSquare H T) ≤
      (2*(r : ℝ)*K+(r : ℝ)*((r : ℝ)-2)*h)*‖T‖^2 := by
  apply KLS.ConstantReduction.inner_apply_le_of_eigenvalues _
    (symmetricCollectiveSquare_isSymmetric H hH)
  intro U lam hU heig
  have hpoly : ∃ y : Space n, tensorPolynomial U.val.ofLp y ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hz := tensorPolynomial_eq_zero_of_symmetric U.val.ofLp U.property hzero
    apply hU
    apply Subtype.ext
    exact PiLp.ext (congrFun hz)
  have heig' : (∑ k, tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ U.val.ofLp)) =
      lam • U.val.ofLp := by
    rw [← symmetricCollectiveSquare_coordinates]
    exact congrArg (fun X : symmetricTensorSubspace n r => X.val.ofLp) heig
  exact collective_eigenvalue_le_of_polynomial_nonzero hr H hH K h lam hK hh U.val.ofLp hpoly heig'

theorem tensorSlotSum_noise_sum_le_symmetric (hr : 2 ≤ r)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ k, (H k).transpose = H k)
    (K h : ℝ)
    (hK : ∀ x : Space n, ‖x‖ = 1 → ∑ k, ‖(H k).toEuclideanLin x‖^2 ≤ K)
    (hh : ∀ x : Space n, ‖x‖ = 1 → ∑ k, (inner ℝ x ((H k).toEuclideanLin x))^2 ≤ h)
    (T : (Fin r → Fin n) → ℝ)
    (hT : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a) :
    (∑ k, (tensorSlotSum (H k) *ᵥ T) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T)) ≤
      (2*(r : ℝ)*K+(r : ℝ)*((r : ℝ)-2)*h)*(T ⬝ᵥ T) := by
  let U : symmetricTensorSubspace n r := ⟨toLp 2 T, hT⟩
  have hb := symmetricCollectiveSquare_inner_le hr H hH K h hK hh U
  rw [symmetricCollectiveSquare_inner H hH] at hb
  change (∑ k, (tensorSlotSum (H k) *ᵥ T) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T)) ≤
      (2*(r : ℝ)*K+(r : ℝ)*((r : ℝ)-2)*h)*‖(toLp 2 T : EuclideanSpace ℝ _)‖^2 at hb
  simpa only [norm_sq_eq_dotProduct] using hb

end KLS.TensorEnergy
end
