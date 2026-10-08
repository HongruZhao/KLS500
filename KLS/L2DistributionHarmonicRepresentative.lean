import KLS.ClassicalLaplacianFromDistribution

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

/-- Weyl regularity for the actual L2 distribution-harmonic limit. The weak
gradient is derived by mollification and energy extraction; no continuity of
the original L2 representative is assumed. -/
theorem exists_smooth_harmonic_representative_of_L2_distribution
    {v : Space n → ℝ} (hv : MemLp v 2 volume) {c : Space n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∫ x, v x * coordinateLaplacian ψ x) = 0) :
    ∃ h : Space n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h (ball c r) ∧
      h =ᵐ[volume.restrict (ball c r)] v ∧
      ∀ x ∈ ball c r, coordinateLaplacian h x = 0 := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  let χ : ContDiffBump c := ⟨r, s, hr, hrs⟩
  have hex (i : Fin n) : ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * v x) i g :=
    distribution_harmonic_cutoff_hasWeakDerivative hv (χ.contDiff : ContDiff ℝ 1 (χ : Space n → ℝ))
      χ.hasCompactSupport hsR (by rw [χ.tsupport_eq]) (fun ψ hψ hc hs _ => hdist ψ hψ hc hs) i
  choose G hG using hex
  have hgrad : HasWeakGradOn (ball c r) v (fun i => G i) :=
    hasWeakGradOn_of_cutoff_eq_one hG (fun x hx => χ.one_of_mem_closedBall (ball_subset_closedBall hx))
  have hdist' : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c r → (∫ x, v x * coordinateLaplacian ψ x) = 0 := by
    intro ψ hψ hc hs
    exact hdist ψ hψ hc (hs.trans (ball_subset_ball hrR.le))
  have hsol := localWeakSol_laplace_of_distribution hv hgrad hdist'
  obtain ⟨h, hh, hae⟩ := exists_contDiffOn_of_localWeakSol isOpen_ball
    (laplaceSmoothOpOn (ball c r)) (f := fun _ => 0) contDiffOn_const
    (fun K _ _ => hv.restrict K) (fun i K _ _ => (Lp.memLp (G i)).restrict K) hgrad hsol
  refine ⟨h, hh, hae, coordinateLaplacian_eq_zero_on_of_contDiffOn_distribution isOpen_ball hh ?_⟩
  intro ψ hψ hc hs
  rw [integral_mul_compact_test_congr_ae_on isOpen_ball.measurableSet hae
    ((tsupport_coordinateLaplacian_subset ψ).trans hs)]
  exact hdist' ψ hψ hc hs

end KLS
end
