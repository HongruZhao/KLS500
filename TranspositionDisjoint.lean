import TranspositionLocalGap

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [DecidableEq I]

theorem inner_edgeDifference_left (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E))
    (x y : E) (i j : I) :
    inner ℝ (edgeDifference ρ x i j) y = inner ℝ x (edgeDifference ρ y i j) := by
  simp only [edgeDifference,inner_sub_left,inner_sub_right,inner_transposition_action]

theorem edgeDifference_twice (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i j : I) :
    edgeDifference ρ (edgeDifference ρ x i j) i j = (2 : ℝ) • edgeDifference ρ x i j := by
  have hinv : ρ (Equiv.swap i j) (ρ (Equiv.swap i j) x) = x := by
    change (ρ (Equiv.swap i j)*ρ (Equiv.swap i j)) x = x
    rw [←map_mul,Equiv.swap_mul_self,map_one]
    rfl
  simp only [edgeDifference,map_sub,hinv]
  module

theorem disjoint_transpositions_commute (i j k l : I)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    (Equiv.swap i j)*(Equiv.swap k l) = (Equiv.swap k l)*(Equiv.swap i j) := by
  ext t
  by_cases hi : t=i
  · subst t
    simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hik,hil,hjk,hjl]
  by_cases hj : t=j
  · subst t
    simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hik,hil,hjk,hjl]
  by_cases hk : t=k
  · subst t
    simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hik.symm,hil.symm,hjk.symm,hjl.symm]
  by_cases hl : t=l
  · subst t
    simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hik.symm,hil.symm,hjk.symm,hjl.symm]
  simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hi,hj,hk,hl]

theorem edgeDifference_commute (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i j k l : I) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    edgeDifference ρ (edgeDifference ρ x k l) i j =
      edgeDifference ρ (edgeDifference ρ x i j) k l := by
  have hc : ρ (Equiv.swap i j) (ρ (Equiv.swap k l) x) =
      ρ (Equiv.swap k l) (ρ (Equiv.swap i j) x) := by
    change (ρ (Equiv.swap i j)*ρ (Equiv.swap k l)) x =
      (ρ (Equiv.swap k l)*ρ (Equiv.swap i j)) x
    rw [←map_mul,←map_mul,disjoint_transpositions_commute i j k l hik hil hjk hjl]
  simp only [edgeDifference,map_sub,hc]
  abel

theorem edgeDifference_inner_nonneg_disjoint
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i j k l : I) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    0 ≤ inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) := by
  have hh := edgeDifference_norm_sq ρ (edgeDifference ρ x k l) i j
  rw [edgeDifference_commute ρ x i j k l hik hil hjk hjl] at hh
  have he : inner ℝ (edgeDifference ρ x k l)
      (edgeDifference ρ (edgeDifference ρ x i j) k l) =
      2 * inner ℝ (edgeDifference ρ x i j) (edgeDifference ρ x k l) := by
    rw [inner_edgeDifference_left,edgeDifference_twice,inner_smul_right,
      ←inner_edgeDifference_left,real_inner_comm (edgeDifference ρ x k l)]
  rw [he] at hh
  nlinarith [sq_nonneg ‖edgeDifference ρ (edgeDifference ρ x i j) k l‖]

end KLS.ConstantReduction
end
