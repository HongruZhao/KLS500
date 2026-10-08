import KLS.MomentDualPairingLimit
import KLS.MomentHarmonicL2Compactness

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma dual_pairing_tendsto_of_strong_cutoff_limit
    {w v : ℕ → Space n → ℝ} {χ ψ g : Space n → ℝ}
    (hw : ∀ j, Continuous (w j)) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hg : MemLp g 2 volume) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hχone : ∀ x ∈ tsupport ψ, χ x = 1)
    (hconv : Tendsto (fun j => eLpNorm ((fun x => χ x * w j x) - g) 2 volume) atTop (𝓝 0))
    (hgap : Tendsto (fun j => ∫ x, (w j x - v j x) * ψ x) atTop (𝓝 0))
    (hv : ∀ᶠ j in atTop, Integrable (fun x => v j x * ψ x)) :
    Tendsto (fun j => ∫ x, v j x * ψ x) atTop (𝓝 (∫ x, g x * ψ x)) := by
  have hf (j : ℕ) : MemLp (fun x => χ x * w j x) 2 volume :=
    (hχ.mul (hw j)).memLp_of_hasCompactSupport hχc.mul_right
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hf hg
    (hψ.memLp_of_hasCompactSupport hψc) hconv
  have hid (j : ℕ) : (∫ x, ψ x * (χ x * w j x)) = ∫ x, w j x * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · rw [hχone x hx, one_mul, mul_comm]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  simp_rw [hid, mul_comm (ψ _) (g _)] at ht
  have hh := ht.sub hgap
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [hv] with j hj
  have hwψ : Integrable (fun x => w j x * ψ x) volume :=
    ((hw j).mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  simp_rw [sub_mul]
  rw [integral_sub hwψ hj]
  ring

/-- The same actual harmonic subsequence has strong primal L2 convergence
and weak convergence of the actual dual error against all nonnegative C1
compact tests. Both limits are the same smooth classical harmonic function. -/
theorem moment_exists_primal_dual_harmonic_subsequence (hn : 0 < n)
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
          (volume.restrict (ball (0 : Space n) (T / 16)))) atTop (𝓝 0) ∧
      ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball (0 : Space n) (T / 16) → (∀ x, 0 ≤ ψ x) →
        Tendsto (fun j => ∫ x, normalizedDualQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j)) x * ψ x)
          atTop (𝓝 (∫ x, h x * ψ x)) := by
  obtain ⟨χ, g, σ, hχ, hχc, hχone, hσ, hconv, hdist⟩ :=
    moment_exists_strong_L2_distribution_harmonic_subsequence hn hLip hc hV hfinite hK hKc hpush
      hε hεlim hT hM hdensity hbound
  obtain ⟨h, hh, hae, hLap⟩ := exists_smooth_harmonic_representative_of_L2_distribution
    (Lp.memLp g) (r := T / 16) (by positivity) (by linarith : T / 16 < T / 8) hdist
  refine ⟨h, σ, hσ, hh, hLap, ?_, ?_⟩
  · apply tendsto_restricted_eLpNorm_of_strong_cutoff_limit isOpen_ball.measurableSet
      (fun x hx => hχone x (ball_subset_closedBall
        (ball_subset_ball (by linarith : T / 16 ≤ T / 8) hx))) hae hconv
  · intro ψ hψ hψc hψs hψ0
    rw [integral_mul_compact_test_congr_ae_on isOpen_ball.measurableSet hae hψs]
    have hs8 := hψs.trans (ball_subset_ball (by linarith : T / 16 ≤ T / 8))
    apply dual_pairing_tendsto_of_strong_cutoff_limit
      (fun j => ((hLip (σ j)).continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const (ε (σ j)))
      hχ.continuous hχc (Lp.memLp g) hψ.continuous hψc
      (fun x hx => hχone x (ball_subset_closedBall (hs8 hx))) hconv
    · exact (moment_primal_dual_pairing_tendsto_zero_on_ball hn hLip hc hV hfinite hK hKc hpush
        hε hεlim hT hM hdensity hbound hψ hψc hs8 hψ0).comp hσ.tendsto_atTop
    · have hsmall : ∀ᶠ j in atTop, ε (σ j) * M ≤ T ^ 2 / 16 := by
        apply (show Tendsto (fun j => ε (σ j) * M) atTop (𝓝 0) by
          simpa using (hεlim.comp hσ.tendsto_atTop).mul_const M).eventually_le_const
        positivity
      filter_upwards [hsmall] with j hj
      let := hfinite (σ j)
      have hstrict := moment_strictConvexOn (hLip (σ j)) (hc (σ j)) (hV (σ j))
        (hK (σ j)).measurableSet (hKc (σ j)) (hpush (σ j))
      exact (continuous_normalizedDualQuadraticError_mul_test (hLip (σ j)).continuous hstrict
        hψ.continuous hT hj
        (fun x hx => abs_sub_quadratic_le_of_normalized_bound (hε (σ j)) (hbound (σ j) x hx))
        (hψs.trans (ball_subset_ball (by linarith : T / 16 ≤ T / 4)))).integrable_of_hasCompactSupport
          hψc.mul_left

end KLS
end
