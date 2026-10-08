import OptSymmetricTensorSpace
import OptPolynomialSphereMaximum
import OptMaximumHessian

/-! Maximum-principle bound for every nonzero homogeneous eigenpolynomial. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise RealInnerProductSpace ContDiff
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

theorem collective_eigenvalue_le_of_polynomial_nonzero (hr : 2 ≤ r)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ k, (H k).transpose = H k)
    (K h lam : ℝ)
    (hK : ∀ x : Space n, ‖x‖ = 1 → ∑ k, ‖(H k).toEuclideanLin x‖^2 ≤ K)
    (hh : ∀ x : Space n, ‖x‖ = 1 → ∑ k, (inner ℝ x ((H k).toEuclideanLin x))^2 ≤ h)
    (T : (Fin r → Fin n) → ℝ)
    (hT : ∃ y : Space n, tensorPolynomial T y ≠ 0)
    (heig : (∑ k, tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ T)) = lam • T) :
    lam ≤ 2*(r : ℝ)*K+(r : ℝ)*((r : ℝ)-2)*h := by
  obtain ⟨c, x, _, hx, hp, hmax⟩ :=
    exists_signed_positive_tensorPolynomial_maximum T (by omega) hT
  let U := c • T
  have heigU : (∑ k, tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ U)) = lam • U := by
    dsimp only [U]
    simp only [Matrix.mulVec_smul, ← Finset.smul_sum, heig, smul_smul]
    rw [mul_comm c lam]
  have hder := KLS.ConstantReduction.derivatives_le_radial_envelope_at_unit
    ((contDiff_tensorPolynomial U).of_le (by simp : (2 : ℕ∞ω) ≤ ⊤)) hr hx hmax
  have hsym (k : Fin q) : inner ℝ x ((H k).toEuclideanLin ((H k).toEuclideanLin x)) =
      ‖(H k).toEuclideanLin x‖^2 := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (show (H k).IsHermitian by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hH k])
    rw [← hs x ((H k).toEuclideanLin x), real_inner_self_eq_norm_sq]
  have hstep (k : Fin q) :
      tensorPolynomial (tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ U)) x ≤
        2*(r : ℝ)*tensorPolynomial U x*‖(H k).toEuclideanLin x‖^2 +
        (r : ℝ)*((r : ℝ)-2)*tensorPolynomial U x*(inner ℝ x ((H k).toEuclideanLin x))^2 := by
    rw [tensorPolynomial_slotSum_square U (H k) (hH k), hder.1, hsym]
    have hb := hder.2 ((H k).toEuclideanLin x)
    linarith
  have heq : lam*tensorPolynomial U x =
      ∑ k, tensorPolynomial (tensorSlotSum (H k) *ᵥ (tensorSlotSum (H k) *ᵥ U)) x := by
    calc
      _ = tensorPolynomial (lam • U) x := (tensorPolynomial_smul lam U x).symm
      _ = _ := by rw [← heigU, tensorPolynomial_sum]
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hstep k)
  rw [← heq] at hbound
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpU : 0 < tensorPolynomial U x := hp
  have hk := mul_le_mul_of_nonneg_left (hK x hx)
    (show 0 ≤ 2*(r : ℝ)*tensorPolynomial U x by positivity)
  have hh' := mul_le_mul_of_nonneg_left (hh x hx)
    (show 0 ≤ (r : ℝ)*((r : ℝ)-2)*tensorPolynomial U x by positivity)
  have hfin : lam*tensorPolynomial U x ≤
      (2*(r : ℝ)*K+(r : ℝ)*((r : ℝ)-2)*h)*tensorPolynomial U x := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hpU).mp hfin

end KLS.TensorEnergy
end
