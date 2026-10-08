import KLS.ViscosityHarmonicLimit
import DifferentialGeometry.Analysis.Viscosity.Distribution

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateLaplacian_eq_second_derivative_sum {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (x : Space n) :
    coordinateLaplacian ψ x = ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro i _
  exact coordinateHessian_eq_fderiv_fderiv
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x) i i

/-- The actual distribution inequality for a globally semiconvex upper-test
subsolution; the test and all derivatives are concrete functions. -/
theorem integral_mul_laplacian_nonneg_of_semiconvex_upper_tests
    {u : Space n → ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    (hsub : ∀ x ∈ U, ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x → 0 ≤ coordinateLaplacian ψ x)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, u x * coordinateLaplacian φ x := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := DifferentialGeometry.Analysis.Viscosity.distribution_le_of_upper_tests_of_convexOn_add_quadratic
    (μ := volume) e A hA hu hU
    (V := fun i : Fin n => fun _ : Space n => EuclideanSpace.single i 1)
    (W := fun _ => 0) (c := fun _ => 0) (r := fun _ => 0)
    (fun _ => contDiffOn_const) contDiffOn_const
    locallyIntegrableOn_zero locallyIntegrableOn_zero
    (fun x hx ψ hψ hm => by
      have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
      have htest := hsub x hx ψ hψ hm
      rw [coordinateLaplacian_eq_second_derivative_sum hψ2] at htest
      simpa using (neg_nonpos.mpr htest)) hφ hφc hφs hφ0
  have hre (i j : Fin n) : e.repr (EuclideanSpace.single i 1) j = if j = i then 1 else 0 := by
    simp [e, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr, PiLp.single_apply]
  have he (i : Fin n) : e i = EuclideanSpace.single i 1 := by
    simp [e, EuclideanSpace.basisFun_apply]
  simp only [hre, he] at h
  simp at h
  have hdiag (k : Fin n) :
      (∑ i : Fin n, ∑ j : Fin n, ∫ x : Space n, u x *
        fderiv ℝ (fderiv ℝ (fun y => if j = k then if i = k then φ y else 0 else 0)) x
          (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) =
      ∫ x : Space n, u x * fderiv ℝ (fderiv ℝ φ) x
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
    classical
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hi
      simp [hi]
    · simp
  simp_rw [hdiag] at h
  have hcont : Continuous u := by
    have hQ : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have heq : u = (fun x => u x + (1 / 2 : ℝ) * A x x) -
      (fun x => (1 / 2 : ℝ) * A x x) := by funext x; simp
    rw [heq]
    exact (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hQ
  have hi (i : Fin n) : Integrable (fun x => u x * coordinateHessian φ x i i) := by
    apply (hcont.mul (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i i).continuous).integrable_of_hasCompactSupport
    exact (hφc.fderiv_apply ℝ _ |>.fderiv_apply ℝ _).mul_left
  have heq : (∫ x, u x * coordinateLaplacian φ x) =
      ∑ i : Fin n, ∫ x, u x *
        fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simp_rw [← coordinateHessian_eq_fderiv_fderiv
      ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _)]
    simp only [coordinateLaplacian, Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun i _ => hi i)
  rw [heq]
  linarith

end KLS
end
