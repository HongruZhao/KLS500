import KLS.DirectionalWordSymmetry
import Mathlib.GroupTheory.Perm.Fin

/-! Finite sums and erased direction lists in the actual word calculus. -/
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalWordDerivative_sum {ι : Type*} (s : Finset ι)
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (vs : List E) (x : E) :
    directionalWordDerivative (fun y => ∑ i ∈ s, f i y) vs x =
      ∑ i ∈ s, directionalWordDerivative (f i) vs x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : directionalWordDerivative (fun y => ∑ i ∈ s, f i y) vs =
        fun y => ∑ i ∈ s, directionalWordDerivative (f i) vs y := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := HasFDerivAt.fun_sum (u := s) (x := x) (fun i hi =>
      (((contDiff_directionalWordDerivative (hf i hi) vs).differentiable
        (by simp)) x).hasFDerivAt)
    rw [hd.fderiv]
    simp only [_root_.sum_apply, directionalWordDerivative_cons]

theorem directionalWordDerivative_const_mul {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (vs : List E) (x : E) :
    directionalWordDerivative (fun y => c * f y) vs x =
      c * directionalWordDerivative f vs x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : directionalWordDerivative (fun y => c * f y) vs =
        fun y => c * directionalWordDerivative f vs y := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := (((contDiff_directionalWordDerivative hf vs).differentiable
      (by simp)) x).hasFDerivAt.const_mul c
    rw [hd.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul, directionalWordDerivative_cons]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem list_ofFn_eraseIdx {k : ℕ} (m : Fin (k + 1) → E) (i : Fin (k + 1)) :
    (List.ofFn m).eraseIdx i.val = List.ofFn (fun j => m (i.succAbove j)) := by
  induction k with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [List.ofFn_succ]
  | succ k ih =>
    induction i using Fin.cases with
    | zero => simp [List.ofFn_succ]
    | succ i =>
      rw [List.ofFn_succ, Fin.val_succ, List.eraseIdx_cons_succ, ih (fun j => m j.succ) i,
        List.ofFn_succ]
      simp [Fin.succ_succAbove_succ]

theorem iteratedFDeriv_linear_mul_zero {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : E →L[ℝ] ℝ) {k : ℕ}
    (m : Fin (k + 1) → E) :
    iteratedFDeriv ℝ (k + 1) (fun y => l y * f y) 0 m =
      ∑ i : Fin (k + 1), l (m i) *
        iteratedFDeriv ℝ k f 0 (fun j => m (i.succAbove j)) := by
  rw [← directionalWordDerivative_ofFn (l.contDiff.mul hf),
    directionalWordDerivative_linear_mul_zero hf]
  simp only [List.length_ofFn]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [list_ofFn_eraseIdx, directionalWordDerivative_ofFn hf]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some]

end KLS
end

#print axioms KLS.directionalWordDerivative_sum
#print axioms KLS.directionalWordDerivative_const_mul
#print axioms KLS.list_ofFn_eraseIdx
#print axioms KLS.iteratedFDeriv_linear_mul_zero
