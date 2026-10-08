import Mathlib

/-! Explicit finite orthonormal projection and its orthogonal remainder.
Both maps are genuine continuous linear maps on the ambient Hilbert space. -/

open scoped BigOperators
noncomputable section
namespace KLS

variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def finiteOrthonormalProjection (v : I → H) : H →L[ℝ] H :=
  ∑ i, (innerSL ℝ (v i)).smulRight (v i)

def finiteOrthonormalRemainder (v : I → H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - finiteOrthonormalProjection v

lemma finiteOrthonormalProjection_apply (v : I → H) (x : H) :
    finiteOrthonormalProjection v x = ∑ i, inner ℝ (v i) x • v i := by
  simp [finiteOrthonormalProjection]

lemma finiteOrthonormalRemainder_apply (v : I → H) (x : H) :
    finiteOrthonormalRemainder v x = x - ∑ i, inner ℝ (v i) x • v i := by
  simp [finiteOrthonormalRemainder, finiteOrthonormalProjection_apply]

lemma inner_finiteOrthonormalRemainder {v : I → H} (hv : Orthonormal ℝ v) (x : H) (i : I) :
    inner ℝ (v i) (finiteOrthonormalRemainder v x) = 0 := by
  rw [finiteOrthonormalRemainder_apply, inner_sub_right, hv.inner_right_fintype]
  exact sub_self _

lemma finiteOrthonormalRemainder_eq_self {v : I → H} {x : H}
    (hx : ∀ i, inner ℝ (v i) x = 0) : finiteOrthonormalRemainder v x = x := by
  simp [finiteOrthonormalRemainder_apply, hx]

lemma finiteOrthonormalProjection_norm_sq {v : I → H} (hv : Orthonormal ℝ v) (x : H) :
    ‖finiteOrthonormalProjection v x‖ ^ 2 = ∑ i, (inner ℝ (v i) x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, finiteOrthonormalProjection_apply, hv.inner_sum]
  simp only [conj_trivial, pow_two]

lemma finiteOrthonormalProjection_remainder_norm_sq {v : I → H} (hv : Orthonormal ℝ v) (x : H) :
    ‖finiteOrthonormalProjection v x‖ ^ 2 + ‖finiteOrthonormalRemainder v x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hi : inner ℝ (finiteOrthonormalProjection v x) (finiteOrthonormalRemainder v x) = 0 := by
    rw [finiteOrthonormalProjection_apply, sum_inner]
    simp only [inner_smul_left, conj_trivial, inner_finiteOrthonormalRemainder hv, mul_zero,
      Finset.sum_const_zero]
  have he : finiteOrthonormalProjection v x + finiteOrthonormalRemainder v x = x := by
    simp only [finiteOrthonormalRemainder, _root_.sub_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hh := norm_add_sq_real (finiteOrthonormalProjection v x) (finiteOrthonormalRemainder v x)
  rw [hi, he] at hh
  linarith

lemma norm_finiteOrthonormalRemainder_le {v : I → H} (hv : Orthonormal ℝ v) (x : H) :
    ‖finiteOrthonormalRemainder v x‖ ≤ ‖x‖ := by
  have hh := finiteOrthonormalProjection_remainder_norm_sq hv x
  nlinarith [norm_nonneg (finiteOrthonormalRemainder v x), norm_nonneg x,
    sq_nonneg ‖finiteOrthonormalProjection v x‖]

end KLS
end
#print axioms KLS.finiteOrthonormalProjection_remainder_norm_sq
#print axioms KLS.norm_finiteOrthonormalRemainder_le
