import KLS.L2DistributionHarmonicRepresentative

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma tendsto_restricted_eLpNorm_of_strong_cutoff_limit
    {w : ℕ → Space n → ℝ} {χ g h : Space n → ℝ} {U : Set (Space n)}
    (hU : MeasurableSet U) (hχone : ∀ x ∈ U, χ x = 1)
    (hae : h =ᵐ[volume.restrict U] g)
    (hconv : Tendsto (fun j => eLpNorm ((fun x => χ x * w j x) - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (w j - h) 2 (volume.restrict U)) atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (w j - h) 2 (volume.restrict U) ≤
      eLpNorm ((fun x => χ x * w j x) - g) 2 volume := by
    have he : eLpNorm (w j - h) 2 (volume.restrict U) =
        eLpNorm ((fun x => χ x * w j x) - g) 2 (volume.restrict U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU, hae] with x hx he
      dsimp only [Pi.sub_apply]
      rw [hχone x hx, one_mul, he]
    rw [he]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ => bot_le) hb

/-- Actual nonlinear compactness in L2: the normalized original weak moment
potentials admit a strictly increasing subsequence converging strongly in L2
on an interior ball to a smooth, classically harmonic function. The subsequence,
limit, weak derivatives, and harmonic equation are all proved, not assumed.
This theorem does not assert pointwise or locally uniform convergence. -/
theorem moment_exists_harmonic_strong_L2_subsequence (hn : 0 < n)
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
      ContDiffOn ℝ (⊤ : ℕ∞) h (ball (0 : Space n) (T / 16)) ∧
      (∀ x ∈ ball (0 : Space n) (T / 16), coordinateLaplacian h x = 0) ∧
      Tendsto (fun j => eLpNorm
        (normalizedQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j)) - h) 2
          (volume.restrict (ball (0 : Space n) (T / 16)))) atTop (𝓝 0) := by
  obtain ⟨χ, g, σ, _, _, hχone, hσ, hconv, hdist⟩ :=
    moment_exists_strong_L2_distribution_harmonic_subsequence hn hLip hc hV hfinite hK hKc hpush
      hε hεlim hT hM hdensity hbound
  obtain ⟨h, hh, hae, hLap⟩ := exists_smooth_harmonic_representative_of_L2_distribution
    (Lp.memLp g) (r := T / 16) (by positivity) (by linarith : T / 16 < T / 8) hdist
  refine ⟨h, σ, hσ, hh, hLap, ?_⟩
  apply tendsto_restricted_eLpNorm_of_strong_cutoff_limit isOpen_ball.measurableSet
    (fun x hx => hχone x (ball_subset_closedBall
      (ball_subset_ball (by linarith : T / 16 ≤ T / 8) hx))) hae hconv

end KLS
end
