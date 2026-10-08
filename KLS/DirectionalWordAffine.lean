import KLS.DirectionalWordAlgebra

/-! Affine pullback and linear operations on actual smooth directional words. -/
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directionalWordDerivative_append (f : E → ℝ) (vs ws : List E) :
    directionalWordDerivative (directionalWordDerivative f ws) vs =
      directionalWordDerivative f (vs ++ ws) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append, directionalWordDerivative, ih]

theorem directionalWordDerivative_sub {f g : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (vs : List E) (x : E) :
    directionalWordDerivative (fun y => f y - g y) vs x =
      directionalWordDerivative f vs x - directionalWordDerivative g vs x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : directionalWordDerivative (fun y => f y - g y) vs =
        fun y => directionalWordDerivative f vs y - directionalWordDerivative g vs y := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := (((contDiff_directionalWordDerivative hf vs).differentiable (by simp)) x).hasFDerivAt.sub
      ((((contDiff_directionalWordDerivative hg vs).differentiable (by simp)) x).hasFDerivAt)
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv

theorem directionalWordDerivative_add {f g : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (vs : List E) (x : E) :
    directionalWordDerivative (fun y => f y + g y) vs x =
      directionalWordDerivative f vs x + directionalWordDerivative g vs x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : directionalWordDerivative (fun y => f y + g y) vs =
        fun y => directionalWordDerivative f vs y + directionalWordDerivative g vs y := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := (((contDiff_directionalWordDerivative hf vs).differentiable (by simp)) x).hasFDerivAt.add
      ((((contDiff_directionalWordDerivative hg vs).differentiable (by simp)) x).hasFDerivAt)
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv

theorem directionalWordDerivative_const_of_ne_nil (c : ℝ) (vs : List E)
    (hne : vs ≠ []) : directionalWordDerivative (fun _ : E => c) vs = 0 := by
  cases vs with
  | nil => exact (hne rfl).elim
  | cons v vs =>
    induction vs generalizing v with
    | nil => funext x; simp [directionalWordDerivative]
    | cons w ws ih =>
      have he := ih w (by simp)
      funext x
      simp only [directionalWordDerivative_cons, he]
      simp

theorem directionalWordDerivative_comp_affine {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : F →L[ℝ] E) (a : E)
    (vs : List F) (x : F) :
    directionalWordDerivative (fun y => f (a + L y)) vs x =
      directionalWordDerivative f (vs.map L) (a + L x) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : directionalWordDerivative (fun y => f (a + L y)) vs =
        fun y => directionalWordDerivative f (vs.map L) (a + L y) := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := (((contDiff_directionalWordDerivative hf (vs.map L)).differentiable
      (by simp)) (a + L x)).hasFDerivAt.comp x (L.hasFDerivAt.const_add a)
    exact congrArg (fun L : F →L[ℝ] ℝ => L v) hd.fderiv

theorem directionalWordDerivative_comp_add_right {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : E) (vs : List E) (x : E) :
    directionalWordDerivative (fun y => f (y+a)) vs x =
      directionalWordDerivative f vs (x+a) := by
  have hmap : vs.map (ContinuousLinearMap.id ℝ E) = vs := by
    change vs.map id = vs
    simp
  have he := directionalWordDerivative_comp_affine hf (ContinuousLinearMap.id ℝ E) a vs x
  rw [hmap] at he
  simpa only [ContinuousLinearMap.id_apply, add_comm] using he

theorem fderiv_fderiv_apply_eq_word {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x u v : E) :
    fderiv ℝ (fderiv ℝ f) x u v = directionalWordDerivative f [u,v] x := by
  have hd := (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)) x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L u) hd.fderiv
  simpa [directionalWordDerivative] using he.symm

end KLS
end
#print axioms KLS.directionalWordDerivative_comp_affine
#print axioms KLS.directionalWordDerivative_sub
