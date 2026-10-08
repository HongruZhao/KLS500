import KLS.ConvexHessian

/-! Convexity from the genuine second Fréchet derivative, including a small
bounded-Hessian perturbation of a uniformly convex potential. -/

open Set Matrix
open scoped BigOperators
open scoped ContDiff
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_univ_of_secondFrechet_nonneg {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ univ f := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline (x v : E) : ConvexOn ℝ univ (fun t : ℝ => f (x + t • v)) := by
    have hp (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hd1 (t : ℝ) := (hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)
    have heq : deriv (fun t : ℝ => f (x + t • v)) =
        fun t => fderiv ℝ f (x + t • v) v := by
      funext t
      exact (hd1 t).deriv
    have hd2 (t : ℝ) : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
        (fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
      simpa using ((hdd (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)).clm_apply
        (hasDerivAt_const t v)
    apply convexOn_univ_of_deriv2_nonneg (f := fun t : ℝ => f (x + t • v))
      (fun t => (hd1 t).differentiableAt)
    · rw [heq]
      exact fun t => (hd2 t).differentiableAt
    · intro t
      change 0 ≤ deriv (deriv (fun t : ℝ => f (x + t • v))) t
      rw [heq, (hd2 t).deriv]
      exact hpos _ _
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (hline x (y - x)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  have heq : x + b • (y - x) = a • x + b • y := by
    have ha' : a = 1 - b := by linarith
    rw [ha']
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    one_smul, add_sub_cancel, heq] using h

theorem secondFrechet_add_const_mul {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + c * g y)) x u v =
      fderiv ℝ (fderiv ℝ f) x u v + c * fderiv ℝ (fderiv ℝ g) x u v := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have he : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfirst : fderiv ℝ (fun y => f y + c * g y) =
      fun y => fderiv ℝ f y + c • fderiv ℝ g y := by
    funext y
    change fderiv ℝ (f + c • g) y = _
    exact ((hd y).hasFDerivAt.add ((he y).hasFDerivAt.const_smul c)).fderiv
  rw [hfirst]
  change fderiv ℝ (fderiv ℝ f + c • fderiv ℝ g) x u v = _
  rw [((hdd x).hasFDerivAt.add ((hee x).hasFDerivAt.const_smul c)).fderiv]
  simp

theorem convexOn_univ_add_small_hessian {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) {κ M c : ℝ}
    (hlower : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hbound : ∀ x v, |fderiv ℝ (fderiv ℝ g) x v v| ≤ M * ‖v‖ ^ 2)
    (hsmall : |c| * M ≤ κ) :
    ConvexOn ℝ univ (fun x => f x + c * g x) := by
  apply convexOn_univ_of_secondFrechet_nonneg (hf.add (contDiff_const.mul hg))
  intro x v
  rw [secondFrechet_add_const_mul hf hg]
  have h := mul_le_mul_of_nonneg_left (hbound x v) (abs_nonneg c)
  have hc := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)
  have hab := neg_abs_le (c * fderiv ℝ (fderiv ℝ g) x v v)
  rw [abs_mul] at hab
  nlinarith [hlower x v]

/-- A uniform operator-norm Hessian bound controls every actual quadratic evaluation. -/
theorem secondFrechet_abs_le_of_opNorm {g : E → ℝ} {M : ℝ}
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) (x v : E) :
    |fderiv ℝ (fderiv ℝ g) x v v| ≤ M * ‖v‖ ^ 2 := by
  calc
    _ = ‖fderiv ℝ (fderiv ℝ g) x v v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fderiv ℝ g) x v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (M * ‖v‖) * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))
    _ = M * ‖v‖ ^ 2 := by ring

/-- The coordinate lower bound used by the weighted spectral development is
exactly a lower bound on genuine second Fréchet evaluations. -/
theorem secondFrechet_lower_of_coordinateHessian {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {κ : ℝ}
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) (x v : Space n) :
    κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ φ) x v v := by
  have h := hlower x (fun i => v i)
  rw [← coordinateHessian_quadratic_eq hφ]
  have he : (fun i => v i) ⬝ᵥ (coordinateHessian φ x *ᵥ (fun i => v i)) =
      ∑ i : Fin n, ∑ j : Fin n, coordinateHessian φ x i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : (fun i => v i) ⬝ᵥ (fun i => v i) = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  rwa [he, hn] at h

end KLS
end
#print axioms KLS.convexOn_univ_of_secondFrechet_nonneg
#print axioms KLS.secondFrechet_add_const_mul
#print axioms KLS.convexOn_univ_add_small_hessian

#print axioms KLS.secondFrechet_abs_le_of_opNorm
#print axioms KLS.secondFrechet_lower_of_coordinateHessian
