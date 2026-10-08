import KLS.SupConvolutionViscosity
import KLS.SemiconvexLaplacianDistribution

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
open DifferentialGeometry.Analysis.Convex
variable {n : ℕ}

lemma tsupport_coordinateLaplacian_subset (φ : Space n → ℝ) :
    tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
  apply (isClosed_tsupport φ).closure_subset_iff.mpr
  intro x hx
  by_contra hn
  apply hx
  unfold coordinateLaplacian
  apply Finset.sum_eq_zero
  intro i _
  change coordinateDerivative (coordinateDerivative φ i) i x = 0
  exact image_eq_zero_of_notMem_tsupport (fun hi => hn
    ((tsupport_coordinateDerivative_subset _ i).trans
      (tsupport_coordinateDerivative_subset φ i) hi))

lemma continuous_supConvolutionOn {u : Space n → ℝ} {s : Set (Space n)}
    (hs : s.Nonempty) (hu : BddAbove (u '' s)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (supConvolutionOn s u ε) := by
  have hc := continuousOn_univ.mp
    ((convexOn_supConvolutionOn_add_norm_sq hs hu hε).continuousOn isOpen_univ)
  have hq : Continuous (fun x : Space n => ‖x‖ ^ 2 / (2 * ε)) := by fun_prop
  convert hc.sub hq using 1
  funext x
  simp

/-- Continuous viscosity subharmonicity implies the concrete distribution
inequality on every strictly smaller concentric ball. -/
theorem integral_mul_laplacian_nonneg_of_continuous_upper_tests_on_ball
    {u : Space n → ℝ} {c : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (closedBall c R))
    (hsub : ∀ x ∈ closedBall c R, ∀ ψ : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x → 0 ≤ coordinateLaplacian ψ x)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball c r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, u x * coordinateLaplacian φ x := by
  let K := closedBall c R
  have hR : 0 < R := hr.trans hrR
  have hK : IsCompact K := isCompact_closedBall c R
  have hne : K.Nonempty := ⟨c, mem_closedBall_self hR.le⟩
  have hbounded := hK.bddAbove_image hu
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hu
  have hM0 : 0 ≤ M := (norm_nonneg (u c)).trans (hM c (mem_closedBall_self hR.le))
  have hbound : ∀ x ∈ K, |u x| ≤ M := by simpa only [Real.norm_eq_abs] using hM
  let δ := (R - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsmallball {x : Space n} (hx : x ∈ ball c r) : closedBall x δ ⊆ interior K := by
    intro y hy
    apply isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall
    have ht := dist_triangle y x c
    have hxy : dist y x ≤ δ := hy
    have hxc : dist x c < r := hx
    change dist y c < R
    dsimp [δ] at hxy
    linarith
  have hineq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 ≤ ∫ x, supConvolutionOn K u ε x * coordinateLaplacian φ x := by
    have ha : 0 < δ ^ 2 / (4 * (M + 1)) := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε he
    change 0 < ε at hε
    let A : Space n →L[ℝ] Space n →L[ℝ] ℝ := ε⁻¹ • (innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    have hA : A.flip = A := by ext v w; simp [A]
    have hconv : ConvexOn ℝ univ (fun x => supConvolutionOn K u ε x + (1 / 2 : ℝ) * A x x) := by
      convert convexOn_supConvolutionOn_add_norm_sq hne hbounded hε using 1
      ext x
      change supConvolutionOn K u ε x + (1 / 2 : ℝ) * (ε⁻¹ * inner ℝ x x) =
        supConvolutionOn K u ε x + ‖x‖ ^ 2 / (2 * ε)
      rw [real_inner_self_eq_norm_sq]
      ring
    apply integral_mul_laplacian_nonneg_of_semiconvex_upper_tests isOpen_ball A hA hconv
      (φ := φ) (hφ := hφ) (hφc := hφc) (hφs := hφs) (hφ0 := hφ0)
    intro x hx ψ hψ hm
    let H : ℝ → (Space n →L[ℝ] ℝ) → (Space n →L[ℝ] Space n →L[ℝ] ℝ) → ℝ :=
      fun _ _ B => -(∑ i : Fin n, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
    have hh := upper_test_supConvolutionOn_of_continuousOn hK hu hM0 hbound hδ hε he
      (hsmallball hx) (H := H) (fun _ _ => monotone_const)
      (fun y hy ρ hρ hmρ => by
        have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by simp)
        have ht := hsub y (interior_subset hy) ρ hρ hmρ
        rw [coordinateLaplacian_eq_second_derivative_sum hρ2] at ht
        exact neg_nonpos.mpr ht) hψ hm
    have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
    rw [coordinateLaplacian_eq_second_derivative_sum hψ2]
    exact neg_nonpos.mp hh
  have hLsupport := tsupport_coordinateLaplacian_subset φ
  have hLc : HasCompactSupport (coordinateLaplacian φ) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) hLsupport
  have hLs : tsupport (coordinateLaplacian φ) ⊆ ball c R :=
    hLsupport.trans (hφs.trans (ball_subset_ball hrR.le))
  have hLi : Integrable (coordinateLaplacian φ) :=
    (continuous_coordinateLaplacian hφ).integrable_of_hasCompactSupport hLc
  have hlimit := (tendstoUniformlyOn_supConvolutionOn_of_continuousOn hK hu).mono
    (subset_tsupport _ |>.trans (hLs.trans ball_subset_closedBall))
  have hfi : Integrable (fun x => coordinateLaplacian φ x • u x) := by
    have hc : Continuous (fun x => coordinateLaplacian φ x * u x) :=
      ((continuous_coordinateLaplacian hφ).continuousOn.mul
        (hu.mono ball_subset_closedBall)).continuous_of_tsupport_subset isOpen_ball
        (tsupport_mul_subset_left.trans hLs)
    simpa only [smul_eq_mul] using hc.integrable_of_hasCompactSupport hLc.mul_right
  have hFi : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Integrable (fun x => coordinateLaplacian φ x • supConvolutionOn K u ε x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Pi.mul_def, smul_eq_mul] using
      ((continuous_coordinateLaplacian hφ).mul (continuous_supConvolutionOn hne hbounded hε)).integrable_of_hasCompactSupport
        hLc.mul_right
  have ht := hlimit.integral_smul hLi hFi hfi
  simp only [smul_eq_mul, mul_comm (coordinateLaplacian φ _) (u _),
    mul_comm (coordinateLaplacian φ _) (supConvolutionOn K u _ _)] at ht
  exact ge_of_tendsto ht hineq

end KLS
end
