import KLS.DistributionHarmonicRegularity

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

/-- Weyl regularity for the actual continuous viscosity-harmonic function.
No weak derivative or local Lipschitz regularity is assumed. -/
theorem IsViscosityHarmonicOn.contDiffOn {U : Set (Space n)} {w : Space n → ℝ}
    (hw : IsViscosityHarmonicOn U w) (hU : IsOpen U) :
    ContDiffOn ℝ (⊤ : ℕ∞) w U := by
  intro c hc
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  let θ : ContDiffBump c := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let v : Space n → ℝ := fun x => θ x * w x
  have hθs : tsupport (θ : Space n → ℝ) ⊆ U := by
    rw [θ.tsupport_eq]
    apply Subset.trans (closedBall_subset_closedBall (show 3 * R / 4 ≤ R by linarith)) hball
  have hvs : tsupport v ⊆ U := tsupport_mul_subset_left.trans hθs
  have hvc : Continuous v :=
    (θ.continuous.continuousOn.mul hw.1).continuous_of_tsupport_subset hU hvs
  have hvcompact : HasCompactSupport v := θ.hasCompactSupport.mul_right
  have hv : MemLp v 2 volume := hvc.memLp_of_hasCompactSupport hvcompact
  have hdist : ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball c (R / 2) → (∀ x, 0 ≤ φ x) →
      (∫ x, v x * coordinateLaplacian φ x) = 0 := by
    intro φ hφ hφc hφs hφ0
    have he := hw.integral_mul_laplacian_eq_zero (by positivity : 0 < R / 2)
      (by linarith : R / 2 < R) hball hφ hφc hφs hφ0
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport (coordinateLaplacian φ)
      · have ht : θ x = 1 := θ.one_of_mem_closedBall (ball_subset_closedBall
          (hφs (tsupport_coordinateLaplacian_subset φ hx)))
        simp only [v, ht, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) v (ball c (R / 4)) :=
    contDiffOn_of_memLp_continuous_distribution_harmonic hv
      (by positivity) (by linarith : R / 4 < R / 2) hvc.continuousOn hdist
  have heq : EqOn v w (ball c (R / 4)) := by
    intro x hx
    have ht : θ x = 1 := θ.one_of_mem_closedBall
      ((ball_subset_ball (show R / 4 ≤ R / 2 by linarith)).trans ball_subset_closedBall hx)
    simp only [v, ht, one_mul]
  exact ((hs.congr heq.symm).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < R / 4)))).contDiffWithinAt

lemma coordinateLaplacian_eq_of_eventuallyEq {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[𝓝 x] g) : coordinateLaplacian f x = coordinateLaplacian g x := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hd : coordinateDerivative f i =ᶠ[𝓝 x] coordinateDerivative g i := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd.fderiv_eq

/-- The original function, everywhere on the open domain, satisfies the
ordinary classical Laplace equation after the derived regularity upgrade. -/
theorem IsViscosityHarmonicOn.coordinateLaplacian_eq_zero
    {U : Set (Space n)} {w : Space n → ℝ} (hw : IsViscosityHarmonicOn U w)
    (hU : IsOpen U) {x : Space n} (hx : x ∈ U) : coordinateLaplacian w x = 0 := by
  have hws := hw.contDiffOn hU
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let θ : ContDiffBump x := ⟨R / 2, R, by positivity, by linarith⟩
  have hθ : IsTestFn U (θ : Space n → ℝ) :=
    ⟨θ.contDiff, θ.hasCompactSupport, by rw [θ.tsupport_eq]; exact hball⟩
  let ψ : Space n → ℝ := fun y => θ y * w y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_mul_of_contDiffOn hU hθ hws
  have heq : ψ =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < R / 2))] with y hy
    have ht : θ y = 1 := θ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp only [ψ, ht, one_mul]
  have h := hw.2 x hx ψ (hψ.of_le (by simp)) heq.self_of_nhds.symm
  have hlo := h.1 (heq.symm.mono (fun _ hh => hh.le))
  have hhi := h.2 (heq.mono (fun _ hh => hh.le))
  rw [coordinateLaplacian_eq_of_eventuallyEq heq] at hlo hhi
  exact le_antisymm hhi hlo

end KLS
end
