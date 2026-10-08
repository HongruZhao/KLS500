import FiniteAverageHilbertVariance
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.ViaEmbedding

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : Type*} [Group G] [Fintype G]

def characterIsometrySum (χ : G →* ℝ) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  ∑ g : G, χ g • ρ g x

theorem characterIsometrySum_action (χ : G →* ℝ) (hχ : ∀ g, χ g * χ g = 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (h : G) :
    ρ h (characterIsometrySum χ ρ x) = χ h • characterIsometrySum χ ρ x := by
  classical
  have he : (∑ g : G, χ (h*g) • ρ (h*g) x) = ∑ g : G, χ g • ρ g x :=
    Equiv.sum_comp (Equiv.mulLeft h) (fun g => χ g • ρ g x)
  calc
    _ = ∑ g : G, χ g • ρ (h*g) x := by
      simp only [characterIsometrySum,map_sum,map_smul,map_mul]
      rfl
    _ = χ h • ∑ g : G, χ (h*g) • ρ (h*g) x := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [smul_smul,χ.map_mul,←mul_assoc,hχ h,one_mul]
    _ = _ := by rw [he]; rfl

theorem characterIsometrySum_norm_sq (χ : G →* ℝ) (hχ : ∀ g, χ g * χ g = 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖characterIsometrySum χ ρ x‖^2 =
      (Fintype.card G : ℝ) * inner ℝ x (characterIsometrySum χ ρ x) := by
  have hp (g : G) : χ g * inner ℝ (ρ g x) (characterIsometrySum χ ρ x) =
      inner ℝ x (characterIsometrySum χ ρ x) := by
    have hh := (ρ g).inner_map_map x (characterIsometrySum χ ρ x)
    rw [characterIsometrySum_action χ hχ ρ x g,inner_smul_right] at hh
    exact hh
  calc
    _ = inner ℝ (∑ g : G, χ g • ρ g x) (characterIsometrySum χ ρ x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ g : G, χ g * inner ℝ (ρ g x) (characterIsometrySum χ ρ x) := by
      simp only [sum_inner,inner_smul_left,conj_trivial]
    _ = _ := by simp only [hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem characterIsometrySum_inner_nonneg (χ : G →* ℝ) (hχ : ∀ g, χ g * χ g = 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    0 ≤ inner ℝ x (characterIsometrySum χ ρ x) := by
  have hh := characterIsometrySum_norm_sq χ hχ ρ x
  have hn : (0:ℝ)<Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith [sq_nonneg ‖characterIsometrySum χ ρ x‖]

end KLS.ConstantReduction
end
