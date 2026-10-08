import SpectralReductionPermutationIndividual

/-! An insertion decomposition using any chosen zero-moving permutations. -/
open Equiv
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem finSuccLiftHom_decompose_of_fix_zero {n : ℕ}
    (σ : Equiv.Perm (Fin (n+1))) (hσ : σ 0 = 0) :
    finSuccLiftHom n (Equiv.Perm.decomposeFin σ).2 = σ := by
  have hp : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e 0)
      (Equiv.Perm.decomposeFin.symm_apply_apply σ)
    change Equiv.Perm.decomposeFin.symm
      ((Equiv.Perm.decomposeFin σ).1, (Equiv.Perm.decomposeFin σ).2) 0 = σ 0 at h
    rw [Equiv.Perm.decomposeFin_symm_apply_zero, hσ] at h
    exact h
  change Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin σ).2) = σ
  rw [← hp]
  exact Equiv.Perm.decomposeFin.symm_apply_apply σ

def insertionDecomposition {n : ℕ} (g : Fin (n+1) → Equiv.Perm (Fin (n+1)))
    (hg : ∀ p, g p 0 = p) :
    Equiv.Perm (Fin (n+1)) ≃ (Fin (n+1) × Equiv.Perm (Fin n)) where
  toFun σ := (σ 0, (Equiv.Perm.decomposeFin ((g (σ 0))⁻¹ * σ)).2)
  invFun v := g v.1 * finSuccLiftHom n v.2
  left_inv σ := by
    have hfix : ((g (σ 0))⁻¹ * σ) 0 = 0 := by
      change (g (σ 0)).symm (σ 0) = 0
      exact (congrArg (g (σ 0)).symm (hg (σ 0))).symm.trans
        ((g (σ 0)).symm_apply_apply 0)
    dsimp only
    rw [finSuccLiftHom_decompose_of_fix_zero _ hfix]
    simp
  right_inv v := by
    rcases v with ⟨p, τ⟩
    have hz : (g p * finSuccLiftHom n τ) 0 = p := by
      rw [Equiv.Perm.mul_apply, finSuccLiftHom_zero, hg]
    change ((g p * finSuccLiftHom n τ) 0,
      (Equiv.Perm.decomposeFin ((g ((g p * finSuccLiftHom n τ) 0))⁻¹ *
        (g p * finSuccLiftHom n τ))).2) = (p, τ)
    rw [hz, inv_mul_cancel_left]
    change (p, (Equiv.Perm.decomposeFin (Equiv.Perm.decomposeFin.symm (0, τ))).2) = _
    rw [Equiv.apply_symm_apply]

@[simp] theorem insertionDecomposition_symm {n : ℕ}
    (g : Fin (n+1) → Equiv.Perm (Fin (n+1))) (hg : ∀ p, g p 0 = p)
    (p : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    (insertionDecomposition g hg).symm (p, τ) = g p * finSuccLiftHom n τ := rfl

end KLS.ConstantReduction
end
