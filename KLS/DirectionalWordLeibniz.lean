import KLS.DirectionalWordAffine

/-! Exact all-order product rule, with each labeled direction assigned to one factor. -/
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Increasing-order subword selected by a Boolean mask on the labeled directions. -/
def maskedDirections : {m : ℕ} → (Fin m → E) → (Fin m → Bool) → List E
  | 0, _, _ => []
  | m+1, h, s => if s 0 then h 0 :: maskedDirections (Fin.tail h) (Fin.tail s)
      else maskedDirections (Fin.tail h) (Fin.tail s)

theorem complement_fin_cons {m : ℕ} (b : Bool) (s : Fin m → Bool) :
    (fun i : Fin (m+1) => !((Fin.cons b s : Fin (m+1) → Bool) i)) = Fin.cons (!b) (fun i => !(s i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem sum_bool_masks {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∑ s, f s) = (∑ s : Fin m → Bool, f (Fin.cons true s)) +
      ∑ s : Fin m → Bool, f (Fin.cons false s) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

/-- Genuine Leibniz formula. Boolean masks are labeled subsets, so repeated directions
still contribute with their correct multiplicities. -/
theorem directionalWordDerivative_mul_masks {f g : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {m : ℕ} (h : Fin m → E) (x : E) :
    directionalWordDerivative (fun y => f y * g y) (List.ofFn h) x =
      ∑ s : Fin m → Bool, directionalWordDerivative f (maskedDirections h s) x *
        directionalWordDerivative g (maskedDirections h (fun i => !(s i))) x := by
  induction m generalizing x with
  | zero => simp [maskedDirections]
  | succ m ih =>
    have he : directionalWordDerivative (fun y => f y * g y) (List.ofFn (Fin.tail h)) =
        fun y => ∑ s : Fin m → Bool,
          directionalWordDerivative f (maskedDirections (Fin.tail h) s) y *
          directionalWordDerivative g (maskedDirections (Fin.tail h) (fun i => !(s i))) y :=
      funext (ih (Fin.tail h))
    rw [List.ofFn_succ, directionalWordDerivative_cons]
    change (fderiv ℝ (directionalWordDerivative (fun y => f y * g y) (List.ofFn (Fin.tail h))) x) (h 0) = _
    rw [he]
    have hd := HasFDerivAt.fun_sum (u := Finset.univ) (x := x) (fun (s : Fin m → Bool) _ =>
      (((contDiff_directionalWordDerivative hf (maskedDirections (Fin.tail h) s)).differentiable
        (by simp)) x).hasFDerivAt.mul
      (((contDiff_directionalWordDerivative hg
        (maskedDirections (Fin.tail h) (fun i => !(s i)))).differentiable (by simp)) x).hasFDerivAt)
    change HasFDerivAt (fun y => ∑ s : Fin m → Bool,
      directionalWordDerivative f (maskedDirections (Fin.tail h) s) y *
      directionalWordDerivative g (maskedDirections (Fin.tail h) (fun i => !(s i))) y) _ x at hd
    rw [hd.fderiv, sum_bool_masks]
    simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
      maskedDirections, Fin.cons_zero, Fin.tail_cons, Bool.false_eq_true,
      ↓reduceIte, complement_fin_cons, Bool.not_true, Bool.not_false]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp only [directionalWordDerivative_cons]
    ring

end KLS
end
#print axioms KLS.directionalWordDerivative_mul_masks
