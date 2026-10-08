import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! A finite-dimensional self-adjoint quadratic form is bounded by its eigenvalues. -/
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem inner_apply_le_of_eigenvalues (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric)
    (B : ℝ) (hB : ∀ (v : E) (lam : ℝ), v ≠ 0 → L v = lam • v → lam ≤ B)
    (x : E) : inner ℝ x (L x) ≤ B*‖x‖^2 := by
  let b := hL.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have hb (i : Fin (Module.finrank ℝ E)) : hL.eigenvalues rfl i ≤ B :=
    hB (b i) (hL.eigenvalues rfl i) (hL.hasEigenvector_eigenvectorBasis rfl i).2
      (hL.apply_eigenvectorBasis rfl i)
  rw [← b.sum_inner_mul_inner x (L x), ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← hL (b i) x, hL.apply_eigenvectorBasis, real_inner_smul_left, real_inner_comm x (b i)]
  have hi := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg (inner ℝ (b i) x))
  simpa only [RCLike.ofReal_real_eq_id, id_eq, real_inner_comm x (b i), pow_two, mul_left_comm, mul_assoc] using hi

end KLS.ConstantReduction
end
