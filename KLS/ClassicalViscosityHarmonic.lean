import KLS.CorrectedHarmonicQuadratic

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateLaplacian_sub_contDiff {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    coordinateLaplacian (fun y => f y - g y) x = coordinateLaplacian f x - coordinateLaplacian g x := by
  simp only [coordinateLaplacian, coordinateHessian_sub hf hg, Finset.sum_sub_distrib]

/-- The actual classical Laplace equation implies both viscosity test
inequalities through the second derivative test at an actual local maximum. -/
theorem isViscosityHarmonicOn_of_contDiff {f : Space n → ℝ} {U : Set (Space n)}
    (hf : ContDiff ℝ 2 f) (hLap : ∀ x ∈ U, coordinateLaplacian f x = 0) :
    IsViscosityHarmonicOn U f := by
  refine ⟨hf.continuous.continuousOn, ?_⟩
  intro x hx ψ hψ he
  constructor
  · intro ht
    have hm : IsLocalMax (fun y => f y - ψ y) x := by
      filter_upwards [ht] with y hy
      rw [he]
      linarith
    have hh := coordinateLaplacian_nonpos_of_isLocalMax (hf.sub hψ) hm
    rw [coordinateLaplacian_sub_contDiff hf hψ, hLap x hx] at hh
    linarith
  · intro ht
    have hm : IsLocalMax (fun y => ψ y - f y) x := by
      filter_upwards [ht] with y hy
      rw [he]
      linarith
    have hh := coordinateLaplacian_nonpos_of_isLocalMax (hψ.sub hf) hm
    rw [coordinateLaplacian_sub_contDiff hψ hf, hLap x hx] at hh
    linarith

end KLS
end
