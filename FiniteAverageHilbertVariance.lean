import KLS.FiniteIsometryAverageAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : Type*} [Group G] [Fintype G]

/-- The literal finite isometry average has the orthogonality identity of
the projection onto invariant vectors. -/
theorem inner_finiteIsometryAverage_self
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    inner ℝ x (finiteIsometryAverage ρ x) = ‖finiteIsometryAverage ρ x‖ ^ 2 := by
  let P := finiteIsometryAverage ρ x
  have hfixed (g : G) : ρ g P = P := finiteIsometryAverage_fixed ρ x g
  have hpair (g : G) : inner ℝ (ρ g x) P = inner ℝ x P := by
    have h := (ρ g).inner_map_map x P
    rw [hfixed] at h
    exact h
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : inner ℝ P P = inner ℝ x P := by
    change inner ℝ ((Fintype.card G : ℝ)⁻¹ • ∑ g : G, ρ g x) P = _
    rw [inner_smul_left, sum_inner]
    simp only [conj_trivial, hpair, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [real_inner_self_eq_norm_sq] at hp
  exact hp.symm

/-- The exact Hilbert variance identity avoids squaring a triangle estimate
for the averaged error. -/
theorem norm_sub_finiteIsometryAverage_sq_eq_average
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 =
      (2 * (Fintype.card G : ℝ))⁻¹ * ∑ g : G, ‖x - ρ g x‖ ^ 2 := by
  classical
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpair : (∑ g : G, inner ℝ x (ρ g x)) =
      (Fintype.card G : ℝ) * ‖finiteIsometryAverage ρ x‖ ^ 2 := by
    have h := inner_finiteIsometryAverage_self ρ x
    unfold finiteIsometryAverage at h
    rw [inner_smul_right, inner_sum] at h
    change (Fintype.card G : ℝ)⁻¹ * (∑ g : G, inner ℝ x (ρ g x)) = _ at h
    field_simp at h
    simpa only [finiteIsometryAverage, one_div] using h
  simp_rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hpair, inner_finiteIsometryAverage_self]
  field_simp
  ring

end KLS.ConstantReduction
end
