import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! A positive symmetric operator with a quadratic square bound has a gap
on the orthogonal complement of its kernel. -/
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem positive_symmetric_gap_finite [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (c : ℝ)
    (hpos : ∀ z, 0 ≤ inner ℝ z (A z))
    (hsquare : ∀ z, c * inner ℝ z (A z) ≤ ‖A z‖^2)
    (x : E) (horth : ∀ z, A z = 0 → inner ℝ x z = 0) :
    c * ‖x‖^2 ≤ inner ℝ x (A x) := by
  let b := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have heig (i : Fin (Module.finrank ℝ E)) :
      A (b i) = hA.eigenvalues rfl i • b i := hA.apply_eigenvectorBasis rfl i
  have hgap (i : Fin (Module.finrank ℝ E)) :
      hA.eigenvalues rfl i = 0 ∨ c ≤ hA.eigenvalues rfl i := by
    have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
    have hp := hpos (b i)
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, hn] at hp
    norm_num only [one_pow, mul_one] at hp
    have hs := hsquare (b i)
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, hn] at hs
    norm_num only [one_pow, mul_one] at hs
    rw [sq_abs] at hs
    by_cases hzero : hA.eigenvalues rfl i = 0
    · exact Or.inl hzero
    · right
      have hl : 0 < hA.eigenvalues rfl i := lt_of_le_of_ne hp (Ne.symm hzero)
      exact le_of_mul_le_mul_right (by simpa only [pow_two] using hs) hl
  rw [← b.sum_sq_inner_right x, Finset.mul_sum, ← b.sum_inner_mul_inner x (A x)]
  apply Finset.sum_le_sum
  intro i _
  rcases hgap i with hz | hc
  · have hk : A (b i) = 0 := by rw [heig, hz, zero_smul]
    have ho := horth (b i) hk
    have ho' : inner ℝ (b i) x = 0 := by rw [real_inner_comm]; exact ho
    simp [ho, ho']
  · rw [← hA (b i) x, heig, real_inner_smul_left, real_inner_comm x (b i)]
    have hi := mul_le_mul_of_nonneg_right hc (sq_nonneg (inner ℝ (b i) x))
    simpa only [RCLike.ofReal_real_eq_id, id_eq, real_inner_comm x (b i), pow_two, mul_left_comm, mul_assoc] using hi

theorem positive_symmetric_gap_on_finite_subspace
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (c : ℝ)
    (hpos : ∀ z, 0 ≤ inner ℝ z (A z))
    (hsquare : ∀ z, c * inner ℝ z (A z) ≤ ‖A z‖^2)
    (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    (hS : ∀ z ∈ S, A z ∈ S) (x : E) (hx : x ∈ S)
    (horth : ∀ z ∈ S, A z = 0 → inner ℝ x z = 0) :
    c * ‖x‖^2 ≤ inner ℝ x (A x) := by
  have hh := positive_symmetric_gap_finite (A.restrict hS) (hA.restrict_invariant hS) c
    (fun z => hpos z) (fun z => hsquare z) (⟨x, hx⟩ : S) (fun z hz => by
      exact horth z z.property (congrArg Subtype.val hz))
  exact hh

end KLS.ConstantReduction
end
