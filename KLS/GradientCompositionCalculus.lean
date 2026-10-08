import KLS.CoordinateDerivativeSymmetry

/-!
# Coordinate chain rules for an actual gradient map

The first and second derivatives of `V ∘ ∇φ` are computed from Fréchet
derivatives. All smoothness assumptions are explicit.
-/

open InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma contDiff_gradient {φ : Space n → ℝ} {k m : ℕ∞ω}
    (hφ : ContDiff ℝ k φ) (hm : m + 1 ≤ k) :
    ContDiff ℝ m (gradient φ) :=
  (toDual ℝ (Space n)).symm.contDiff.comp (hφ.fderiv_right hm)

lemma fderiv_space_coordinate {g : Space n → Space n} {x : Space n}
    (hg : DifferentiableAt ℝ g x) (a : Fin n) (v : Space n) :
    fderiv ℝ (fun y => g y a) x v = fderiv ℝ g x v a := by
  have h := (EuclideanSpace.proj a).hasFDerivAt.comp x hg.hasFDerivAt
  simpa only [EuclideanSpace.coe_proj, ContinuousLinearMap.comp_apply, Function.comp_def] using
    congrArg (fun D => D v) h.fderiv

lemma coordinateDerivative_comp {f : Space n → ℝ} {g : Space n → Space n}
    {x : Space n} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f (g y)) i x =
      ∑ a, coordinateDerivative f a (g x) *
        coordinateDerivative (fun y => g y a) i x := by
  change fderiv ℝ (f ∘ g) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x hf hg, ContinuousLinearMap.comp_apply, ← inner_gradient_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    coordinateDerivative_eq_gradient]
  apply Finset.sum_congr rfl
  intro a _
  rw [← coordinateDerivative_eq_gradient (fun y => g y a)]
  rw [coordinateDerivative, fderiv_space_coordinate hg]
  ring

lemma coordinateDerivative_comp_gradient {V φ : Space n → ℝ}
    (hV : Differentiable ℝ V) (hφ : ContDiff ℝ 2 φ) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => V (gradient φ y)) i x =
      ∑ a, coordinateDerivative V a (gradient φ x) * coordinateHessian φ x i a := by
  rw [coordinateDerivative_comp (hV _) ((contDiff_gradient hφ (m := 1)
    (by norm_num)).differentiable (by norm_num) x)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  congr 1
  funext y
  exact (coordinateDerivative_eq_gradient φ a y).symm

/-- The full Hessian chain rule through the actual gradient map. -/
theorem coordinateHessian_comp_gradient {V φ : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (hφ : ContDiff ℝ 3 φ) (i j : Fin n) (x : Space n) :
    coordinateHessian (fun y => V (gradient φ y)) x i j =
      (∑ a, ∑ b, coordinateHessian V (gradient φ x) a b *
        coordinateHessian φ x i a * coordinateHessian φ x j b) +
      ∑ a, coordinateDerivative V a (gradient φ x) *
        coordinateDerivative (fun y => coordinateHessian φ y i j) a x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hgrad : ContDiff ℝ 2 (gradient φ) := contDiff_gradient hφ (by norm_num)
  have hDV (a : Fin n) : ContDiff ℝ 1 (coordinateDerivative V a) :=
    contDiff_coordinateDerivative hV (by norm_num) a
  have hH (a b : Fin n) : ContDiff ℝ 1 (fun y => coordinateHessian φ y a b) :=
    contDiff_coordinateHessian hφ (by norm_num) a b
  have hfirst : coordinateDerivative (fun y => V (gradient φ y)) j =
      fun y => ∑ a, coordinateDerivative V a (gradient φ y) * coordinateHessian φ y j a :=
    funext (coordinateDerivative_comp_gradient (hV.differentiable (by norm_num)) hφ2 j)
  change coordinateDerivative (coordinateDerivative (fun y => V (gradient φ y)) j) i x = _
  rw [hfirst, coordinateDerivative_sum
    (f := fun a y => coordinateDerivative V a (gradient φ y) * coordinateHessian φ y j a)
    (fun a => (((hDV a).comp (hgrad.of_le (by norm_num))).differentiable (by norm_num) x).mul
      ((hH j a).differentiable (by norm_num) x))]
  have hterm (a : Fin n) :
      coordinateDerivative (fun y => coordinateDerivative V a (gradient φ y) *
        coordinateHessian φ y j a) i x =
      (∑ b, coordinateHessian V (gradient φ x) b a * coordinateHessian φ x i b) *
        coordinateHessian φ x j a + coordinateDerivative V a (gradient φ x) *
        coordinateDerivative (fun y => coordinateHessian φ y i j) a x := by
    rw [coordinateDerivative_mul
      (f := fun y => coordinateDerivative V a (gradient φ y))
      (g := fun y => coordinateHessian φ y j a)
      (((hDV a).comp (hgrad.of_le (by norm_num))).differentiable (by norm_num) x)
      ((hH j a).differentiable (by norm_num) x),
      coordinateDerivative_comp_gradient ((hDV a).differentiable (by norm_num)) hφ2,
      coordinateDerivative_hessian_cycle hφ]
    rfl
  simp_rw [hterm, Finset.sum_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

end KLS
end

#print axioms KLS.contDiff_gradient
#print axioms KLS.coordinateDerivative_comp_gradient
#print axioms KLS.coordinateHessian_comp_gradient
