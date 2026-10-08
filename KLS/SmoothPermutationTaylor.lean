import KLS.DirectionalWordAlgebra

/-! Exact averaging over every permutation, with the distinguished linear
slot first. The factorial counts are derived from the actual permutation
bijection and smooth mixed-derivative symmetry. -/
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_permutation_head_sum_succ {g : E → E → ℝ}
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (g v)) (d : ℕ)
    (m : Fin (d + 2) → E) (x : E) :
    (∑ σ : Equiv.Perm (Fin (d + 2)), iteratedFDeriv ℝ (d + 1)
      (g (m (σ 0))) x (fun j => m (σ j.succ))) =
      ((d + 1).factorial : ℝ) * ∑ i : Fin (d + 2),
        iteratedFDeriv ℝ (d + 1) (g (m i)) x (fun j => m (i.succAbove j)) := by
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin' (n := d)).symm,
    Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, Equiv.Perm.decomposeFin'Symm_zero,
    Equiv.Perm.decomposeFin'Symm_succ]
  simp_rw [show ∀ (i : Fin (d + 2)) (σ : Equiv.Perm (Fin (d + 1))),
    iteratedFDeriv ℝ (d + 1) (g (m i)) x
      (fun j => m (i.succAbove (σ j))) =
    iteratedFDeriv ℝ (d + 1) (g (m i)) x (fun j => m (i.succAbove j)) from
      fun i σ => smooth_iteratedFDeriv_comp_perm (hg (m i))
        (fun j => m (i.succAbove j)) σ x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- The exact averaging identity includes order zero. -/
theorem smooth_permutation_head_sum {g : E → E → ℝ}
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (g v)) (d : ℕ)
    (m : Fin (d + 1) → E) (x : E) :
    (∑ σ : Equiv.Perm (Fin (d + 1)), iteratedFDeriv ℝ d
      (g (m (σ 0))) x (fun j => m (σ j.succ))) =
      (d.factorial : ℝ) * ∑ i : Fin (d + 1),
        iteratedFDeriv ℝ d (g (m i)) x (fun j => m (i.succAbove j)) := by
  cases d with
  | zero =>
    have hσ (σ : Equiv.Perm (Fin 1)) : σ = 1 := by
      apply Equiv.ext
      intro i
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 1))]
    · simp
    · intro σ _ hne
      exact (hne (hσ σ)).elim
    · simp
  | succ d => exact smooth_permutation_head_sum_succ hg d m x

/- Permutation averaging is independent of whether the distinguished
observable index is placed first or last. This is a literal finite reindex. -/
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_permutation_head_eq_last {d : ℕ}
    (F : E → (Fin d → E) → ℝ) (m : Fin (d + 1) → E) :
    (∑ σ : Equiv.Perm (Fin (d + 1)), F (m (σ 0))
      (fun j => m (σ j.succ))) =
    ∑ σ : Equiv.Perm (Fin (d + 1)), F (m (σ (Fin.last d)))
      (fun j => m (σ j.castSucc)) := by
  let ρ := (finRotate (d + 1)).symm
  have hzero : ρ 0 = Fin.last d := by
    apply (finRotate (d + 1)).symm_apply_eq.mpr
    exact finRotate_last'.symm
  have hsucc (j : Fin d) : ρ j.succ = j.castSucc := by
    apply (finRotate (d + 1)).symm_apply_eq.mpr
    exact (finRotate_of_lt j.isLt).symm
  rw [← Equiv.sum_comp (Equiv.mulRight ρ)]
  apply Finset.sum_congr rfl
  intro σ _
  change F (m (σ (ρ 0))) (fun j => m (σ (ρ j.succ))) = _
  simp only [hzero, hsucc]

end KLS
end
#print axioms KLS.smooth_permutation_head_sum_succ
#print axioms KLS.smooth_permutation_head_sum
#print axioms KLS.sum_permutation_head_eq_last
