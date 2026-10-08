import KLS.WeakMomentLogDetTrace
import KLS.HessianMetricEvolution
import KLS.C2BarrierComparison
import DifferentialGeometry.Analysis.Viscosity.Distribution

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma sum_row_secondDerivative_eq_trace {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (R : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    (∑ k : Fin n, fderiv ℝ (fderiv ℝ ψ) x
      (WithLp.toLp 2 (R k)) (WithLp.toLp 2 (R k))) =
      (R.transpose * R * coordinateHessian ψ x).trace := by
  simp_rw [← coordinateHessian_quadratic_eq hψ]
  rw [trace_mul_hessian_eq_sum hψ]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change coordinateHessian ψ x i j * R k i * R k j =
    (R k i * R k j) * coordinateHessian ψ x i j
  ring

/-- Every constant positive-semidefinite trace operator transfers from
upper tests of a convex function to its actual distribution. A continuous
right side suffices; no Lipschitz derivative is assumed. -/
theorem integral_trace_lower_of_convex_upper_tests
    {u f : Space n → ℝ} (hc : ConvexOn ℝ univ u) (hf : Continuous f)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.PosSemidef)
    (hsub : ∀ x : Space n, ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x → f x ≤ (J * coordinateHessian ψ x).trace)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫ x, f x * χ x) ≤ ∫ x, u x * (J * coordinateHessian χ x).trace := by
  classical
  obtain ⟨R,_hRs,hRR⟩ := exists_symmetric_matrix_square_root hJ
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hconv : ConvexOn ℝ univ (fun x => u x + (1/2 : ℝ) *
      (0 : Space n →L[ℝ] Space n →L[ℝ] ℝ) x x) := by simpa using hc
  have hh := DifferentialGeometry.Analysis.Viscosity.distribution_le_of_upper_tests_of_convexOn_add_quadratic
    (μ := volume) e 0 (by rfl) hconv isOpen_univ
    (V := fun k : Fin n => fun _ : Space n => WithLp.toLp 2 (R k))
    (W := fun _ => 0) (c := fun _ => 0) (r := fun x => -f x)
    (fun _ => contDiffOn_const) contDiffOn_const locallyIntegrableOn_zero
    (hf.neg.locallyIntegrable.locallyIntegrableOn univ)
    (fun x _ ψ hψ hm => by
      have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
      rw [sum_row_secondDerivative_eq_trace hψ2 R x,hRR]
      simpa using neg_le_neg (hsub x ψ hψ hm))
    hχ hχc (subset_univ _) hχ0
  have hre (k i : Fin n) : e.repr (WithLp.toLp 2 (R k) : Space n) i = R k i := by
    simp [e,EuclideanSpace.basisFun_toBasis,PiLp.basisFun_repr]
  have he (i : Fin n) : e i = EuclideanSpace.single i 1 := by
    simp [e,EuclideanSpace.basisFun_apply]
  simp only [hre,he] at hh
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_mul, fderiv_fun_const,
    _root_.zero_apply, mul_zero, integral_zero, Finset.sum_const_zero, sub_zero,
    sub_neg_eq_add, zero_add, neg_add_le_iff_le_add, add_zero] at hh
  have hu : Continuous u := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  have hi (i j : Fin n) : Integrable (fun x => u x * coordinateHessian χ x i j) := by
    apply (hu.mul (contDiff_coordinateHessian hχ (m := 0) (by norm_num) i j).continuous).integrable_of_hasCompactSupport
    exact (hχc.fderiv_apply ℝ _ |>.fderiv_apply ℝ _).mul_left
  have hder (k i j : Fin n) (x : Space n) :
      fderiv ℝ (fderiv ℝ (fun y => R k i * R k j * χ y)) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
        R k i * R k j * coordinateHessian χ x i j := by
    rw [← coordinateHessian_eq_fderiv_fderiv
      (((contDiff_const.mul hχ).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
    exact coordinateHessian_smul hχ (R k i * R k j) x j i |>.trans
      (by rw [(coordinateHessian_symmetric hχ x).apply j i])
  simp_rw [hder] at hh
  have hijk (k i j : Fin n) : Integrable
      (fun x => u x * (R k i * R k j * coordinateHessian χ x i j)) := by
    convert (hi i j).const_mul (R k i * R k j) using 1
    funext x
    ring
  have hpoint (x : Space n) : (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      u x * (R k i * R k j * coordinateHessian χ x i j)) =
      u x * (J * coordinateHessian χ x).trace := by
    have hs := sum_row_secondDerivative_eq_trace hχ R x
    simp_rw [← coordinateHessian_quadratic_eq hχ] at hs
    rw [hRR] at hs
    rw [← hs]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change u x * (R k i * R k j * coordinateHessian χ x i j) =
      u x * (coordinateHessian χ x i j * R k i * R k j)
    ring
  have heq : (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      ∫ x, u x * (R k i * R k j * coordinateHessian χ x i j)) =
      ∫ x, u x * (J * coordinateHessian χ x).trace := by
    rw [show (fun x => u x * (J * coordinateHessian χ x).trace) =
      (fun x => ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        u x * (R k i * R k j * coordinateHessian χ x i j)) from funext (fun x => (hpoint x).symm)]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hijk k i j)))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hijk k i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hijk k i j)]
  rw [heq] at hh
  linarith

end KLS
end
