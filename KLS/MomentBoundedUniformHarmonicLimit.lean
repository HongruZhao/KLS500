import KLS.MomentUniformHarmonicLimit

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The harmonic limit retains the original uniform bound on the compact
inner ball; this supplies the actual size input for quantitative Taylor bounds. -/
theorem moment_exists_bounded_uniform_harmonic_subsequence (hn : 0 < n)
    {u V : ℕ → Space n → ℝ} {L : ℕ → ℝ≥0}
    (hLip : ∀ j, LipschitzWith (L j) (u j))
    (hc : ∀ j, ConvexOn ℝ univ (u j)) (hV : ∀ j, Continuous (V j))
    (hfinite : ∀ j, IsFiniteMeasure (potentialMeasure (u j)))
    {K : ℕ → Set (Space n)} (hK : ∀ j, IsClosed (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hpush : ∀ j, MomentMap.gradientPushforward (u j) = (potentialMeasure (V j)).restrict (K j))
    {c ε : ℕ → ℝ} {T M : ℝ}
    (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) (hT : 0 < T) (hM : 0 ≤ M)
    (hdensity : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |Real.exp (-u j x + V j (gradient (u j) x)) - 1| ≤ (ε j) ^ 2)
    (hbound : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |normalizedQuadraticError (u j) 0 0 (c j) (ε j) x| ≤ M) :
    ∃ (h : Space n → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧
      ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ x ∈ ball (0 : Space n) (T / 32), coordinateLaplacian h x = 0) ∧
      TendstoUniformlyOn
        (fun j => normalizedQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j)))
        h atTop (closedBall (0 : Space n) (T / 64)) ∧
      ∀ x ∈ closedBall (0 : Space n) (T / 64), |h x| ≤ M := by
  obtain ⟨h, σ, hσ, hh, hLap, hconv⟩ := moment_exists_uniform_harmonic_subsequence hn hLip hc hV
    hfinite hK hKc hpush hε hεlim hT hM hdensity hbound
  refine ⟨h, σ, hσ, hh, hLap, hconv, ?_⟩
  intro x hx
  apply le_of_tendsto (hconv.tendsto_at hx).abs
  exact Eventually.of_forall fun j => hbound (σ j) x
    (closedBall_subset_closedBall (by linarith : T / 64 ≤ T) hx)

end KLS
end
