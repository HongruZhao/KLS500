import KLS.DirectionalWordCalculus
import Mathlib.Data.List.FinRange

/-! Smooth mixed derivatives commute, including arbitrary permutation of
directions, and the literal word calculus agrees with iteratedFDeriv. -/
open scoped ContDiff Topology
noncomputable section
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalWordDerivative_swap {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : E) (vs : List E) :
    directionalWordDerivative f (a :: b :: vs) =
      directionalWordDerivative f (b :: a :: vs) := by
  let g := directionalWordDerivative f vs
  have hg := contDiff_directionalWordDerivative hf vs
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by simp)
  have hgd : Differentiable ℝ (fderiv ℝ g) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  funext x
  change fderiv ℝ (fun y => fderiv ℝ g y b) x a =
    fderiv ℝ (fun y => fderiv ℝ g y a) x b
  rw [fderiv_clm_apply (hgd x) (differentiableAt_const _),
    fderiv_clm_apply (hgd x) (differentiableAt_const _)]
  simpa using (hg2.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) |>.eq a b

theorem directionalWordDerivative_perm {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {vs ws : List E} (hp : vs.Perm ws) :
    directionalWordDerivative f vs = directionalWordDerivative f ws := by
  induction hp with
  | nil => rfl
  | cons a hp ih => simp only [directionalWordDerivative, ih]
  | swap a b vs => exact directionalWordDerivative_swap hf b a vs
  | trans hp hq ihp ihq => exact ihp.trans ihq

theorem directionalWordDerivative_ofFn {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {k : ℕ} (m : Fin k → E) (x : E) :
    directionalWordDerivative f (List.ofFn m) x = iteratedFDeriv ℝ k f x m := by
  induction k generalizing x with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directionalWordDerivative f (List.ofFn (Fin.tail m))) x (m 0) = _
    have he : directionalWordDerivative f (List.ofFn (Fin.tail m)) =
        fun y => iteratedFDeriv ℝ k f y (Fin.tail m) := funext (ih (Fin.tail m))
    rw [he]
    have hdiff := ((hf.iteratedFDeriv_right (i := k) (m := (1 : ℕ∞ω))
      (by simp)).differentiable (by norm_num)) x
    exact (hdiff.iteratedFDeriv_succ_apply_left' (m := m)).symm

/-- Arbitrary-order permutation symmetry needs only genuine C∞ smoothness,
as proved by commuting adjacent actual second derivatives. -/
theorem smooth_iteratedFDeriv_comp_perm {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {k : ℕ} (m : Fin k → E)
    (σ : Equiv.Perm (Fin k)) (x : E) :
    iteratedFDeriv ℝ k f x (m ∘ σ) = iteratedFDeriv ℝ k f x m := by
  rw [← directionalWordDerivative_ofFn hf, ← directionalWordDerivative_ofFn hf]
  exact congrFun (directionalWordDerivative_perm hf (σ.ofFn_comp_perm m)) x

end KLS
end

#print axioms KLS.directionalWordDerivative_swap
#print axioms KLS.directionalWordDerivative_perm
#print axioms KLS.directionalWordDerivative_ofFn
#print axioms KLS.smooth_iteratedFDeriv_comp_perm
