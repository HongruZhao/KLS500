import KLS.MomentL2HarmonicLimit
import KLS.WeightedStrongL2Compactness
import KLS.WeightedDistributionHarmonicLimit

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual weighted strong-L2 subsequence has a distribution-harmonic limit. -/
theorem weighted_exists_strong_L2_distribution_harmonic_subsequence (hn : 0 < n)
    {u W V : ℕ → Space n → ℝ} {L : ℕ → ℝ≥0}
    (hLip : ∀ j, LipschitzWith (L j) (u j))
    (hu : ∀ j, ContDiff ℝ 1 (u j)) (hc : ∀ j, StrictConvexOn ℝ univ (u j))
    (hW : ∀ j, Continuous (W j)) (hV : ∀ j, Continuous (V j))
    {K : ℕ → Set (Space n)} (hK : ∀ j, IsClosed (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hpush : ∀ j, (potentialMeasure (W j)).map (gradient (u j)) = (potentialMeasure (V j)).restrict (K j))
    {c ε : ℕ → ℝ} {T M : ℝ}
    (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) (hT : 0 < T) (hM : 0 ≤ M)
    (hdensity : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |Real.exp (-W j x + V j (gradient (u j) x)) - 1| ≤ (ε j) ^ 2)
    (hbound : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |normalizedQuadraticError (u j) 0 0 (c j) (ε j) x| ≤ M) :
    ∃ (χ : Space n → ℝ) (g : Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ),
      ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      (∀ x ∈ closedBall (0 : Space n) (T / 8), χ x = 1) ∧ StrictMono σ ∧
      Tendsto (fun j => eLpNorm
        ((fun x => χ x * normalizedQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j)) x) -
          (g : Space n → ℝ)) 2 volume) atTop (𝓝 0) ∧
      ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball (0 : Space n) (T / 8) →
        (∫ x, g x * coordinateLaplacian ψ x) = 0 := by
  let χ : ContDiffBump (0 : Space n) := ⟨T / 8, T / 4, by positivity, by linarith⟩
  obtain ⟨g, σ, hσ, hconv⟩ := weighted_exists_strong_L2_subsequence_of_cutoff hn
    hLip hu hc hW hV hK hKc hpush hε hεlim (R := T / 2) (r := T / 4) (T := T)
    (by positivity) (by linarith) (by linarith) hM hdensity hbound χ.contDiff χ.hasCompactSupport
    (by rw [χ.tsupport_eq])
  refine ⟨χ, g, σ, χ.contDiff, χ.hasCompactSupport, fun _ hx => χ.one_of_mem_closedBall hx,
    hσ, hconv, ?_⟩
  intro ψ hψ hψc hψs
  apply laplacian_pairing_zero_of_strong_cutoff_limit
    (fun j => ((hLip (σ j)).continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const (ε (σ j)))
    χ.continuous χ.hasCompactSupport (Lp.memLp g) hψ hψc
    (fun _ hx => χ.one_of_mem_closedBall (ball_subset_closedBall (hψs hx))) hconv
  exact (weighted_normalized_laplacian_pairing_tendsto_zero_on_ball hn hLip hu hc hW hV hK hKc hpush
    hε hεlim hT hM hdensity hbound hψ hψc (hψs.trans ball_subset_closedBall)).comp hσ.tendsto_atTop

end KLS
end
