import KLS.SecondOrderLocalTaylor

/-! Actual calculus of symmetric quadratic polynomials without positivity.
This allows the local Taylor remainder to be used before the sign of a test
Hessian has been established. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma gradient_centeredQuadratic_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    gradient (centeredQuadratic A x₀ p c) x = p + matrixAction A (x - x₀) := by
  have hsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)
  have hz : HasFDerivAt (fun y : Space n => y - x₀) (ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).sub_const x₀
  have hAz : HasFDerivAt (fun y : Space n => matrixAction A (y - x₀)) (matrixAction A) x := by
    convert (matrixAction A).hasFDerivAt.comp x hz using 1 <;> simp [Function.comp_def]
  have hp : HasFDerivAt (fun y : Space n => inner ℝ p (y - x₀)) (innerSL ℝ p) x := by
    convert (innerSL ℝ p).hasFDerivAt.comp x hz using 1 <;> simp [Function.comp_def]
  have hd := (hp.const_add c).add ((hz.inner ℝ hAz).const_mul (1 / 2 : ℝ))
  change HasFDerivAt (centeredQuadratic A x₀ p c) _ x at hd
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, fderivInnerCLM_apply,
    innerSL_apply_apply, inner_add_left, smul_eq_mul]
  have hs : inner ℝ (matrixAction A (x - x₀)) v =
      inner ℝ (x - x₀) (matrixAction A v) := hsym _ _
  rw [← hs, real_inner_comm v (matrixAction A (x - x₀))]
  ring

lemma coordinateHessian_centeredQuadratic_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    coordinateHessian (centeredQuadratic A x₀ p c) x = A := by
  ext i j
  have heq : coordinateDerivative (centeredQuadratic A x₀ p c) j =
      fun y : Space n => p j + (matrixAction A (y - x₀)) j := by
    funext y
    rw [coordinateDerivative_eq_gradient, gradient_centeredQuadratic_of_isSymm hA]
    rfl
  change coordinateDerivative (coordinateDerivative (centeredQuadratic A x₀ p c) j) i x = _
  rw [heq]
  have hd : HasFDerivAt (fun y : Space n => p j + (matrixAction A (y - x₀)) j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (matrixAction A)) x := by
    convert (((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
      ((matrixAction A).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))).const_add (p j)) using 1 <;>
      simp
  rw [coordinateDerivative, hd.fderiv]
  change (matrixAction A (EuclideanSpace.single i 1)) j = A i j
  simp only [matrixAction_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact hA.apply i j

lemma coordinateHessian_isSymm_of_contDiffAt {F : Space n → ℝ} {x : Space n}
    (hF : ContDiffAt ℝ 2 F x) : (coordinateHessian F x).IsSymm := by
  have hd := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply Matrix.IsSymm.ext
  intro i j
  rw [coordinateHessian_eq_fderiv_fderiv hd, coordinateHessian_eq_fderiv_fderiv hd]
  exact (hF.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Actual local Taylor estimate for every C2 function, without a sign
assumption on its Hessian. -/
theorem eventually_abs_sub_quadratic_taylor_le_sq
    {F : Space n → ℝ} {x₀ : Space n} (hF : ContDiffAt ℝ 2 F x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x₀,
      |F y - centeredQuadratic (coordinateHessian F x₀) x₀ (gradient F x₀) (F x₀) y| ≤
        ε * ‖y - x₀‖ ^ 2 := by
  have hs := coordinateHessian_isSymm_of_contDiffAt hF
  let q := centeredQuadratic (coordinateHessian F x₀) x₀ (gradient F x₀) (F x₀)
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hqd : DifferentiableAt ℝ q x₀ := hq.differentiable (by norm_num) x₀
  have hFd : DifferentiableAt ℝ F x₀ := hF.differentiableAt (by norm_num)
  have hfirst : fderiv ℝ F x₀ = fderiv ℝ q x₀ := by
    ext v
    rw [← inner_gradient_left, ← inner_gradient_left, gradient_centeredQuadratic_of_isSymm hs]
    simp
  have hsecond : fderiv ℝ (fderiv ℝ F) x₀ = fderiv ℝ (fderiv ℝ q) x₀ := by
    apply secondFrechet_eq_of_coordinateHessian_eq
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀)
    exact (coordinateHessian_centeredQuadratic_of_isSymm hs _ _ _ _).symm
  have hfirstzero : fderiv ℝ (fun y => F y - q y) x₀ = 0 := by
    change fderiv ℝ (F - q) x₀ = 0
    rw [fderiv_sub hFd hqd, hfirst, sub_self]
  have hsecondzero : fderiv ℝ (fderiv ℝ (fun y => F y - q y)) x₀ = 0 := by
    have hevent : fderiv ℝ (fun y => F y - q y) =ᶠ[𝓝 x₀]
        (fun y => fderiv ℝ F y - fderiv ℝ q y) := by
      filter_upwards [hF.eventually (by norm_num)] with y hy
      exact fderiv_sub (hy.differentiableAt (by norm_num)) (hq.differentiable (by norm_num) y)
    rw [hevent.fderiv_eq]
    change fderiv ℝ (fderiv ℝ F - fderiv ℝ q) x₀ = 0
    rw [fderiv_sub
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀),
      hsecond, sub_self]
  exact eventually_abs_le_sq_of_zero_second_jet (hF.sub hq.contDiffAt)
    (by simp [q]) hfirstzero hsecondzero hε

end KLS
end

#print axioms KLS.gradient_centeredQuadratic_of_isSymm
#print axioms KLS.eventually_abs_sub_quadratic_taylor_le_sq
