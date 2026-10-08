import KLS.MomentRadialAverageSandwich
import KLS.UniformLimitFromRadialSandwich
import KLS.WeightedL1Compactness
import KLS.HarmonicInteriorGradient

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Original finite-mass weak moment data with quadratic flatness and density
error of order epsilon squared have an actual locally uniform harmonic
subsequence. No compactness, mean-value, or convergence premise is assumed. -/
theorem moment_exists_uniform_harmonic_subsequence (hn : 0 < n)
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
        h atTop (closedBall (0 : Space n) (T / 64)) := by
  obtain ⟨χ₀, g, σ, hχ₀, hχ₀c, hχ₀one, hσ, hconv, hdist⟩ :=
    moment_exists_strong_L2_distribution_harmonic_subsequence hn hLip hc hV hfinite hK hKc hpush
      hε hεlim hT hM hdensity hbound
  obtain ⟨f, hf, hfg, hfLap⟩ := exists_smooth_harmonic_representative_of_L2_distribution
    (Lp.memLp g) (r := T / 16) (by positivity) (by linarith : T / 16 < T / 8) hdist
  have hSU : closedBall (0 : Space n) (3 * T / 64) ⊆ ball (0 : Space n) (T / 16) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨h, hh, hhf⟩ := exists_global_smooth_eq_near_compact isOpen_ball hf
    (isCompact_closedBall (0 : Space n) (3 * T / 64)) hSU
  refine ⟨h, σ, hσ, hh, ?_, ?_⟩
  · intro x hx
    have hxS : x ∈ closedBall (0 : Space n) (3 * T / 64) :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hx)
    rw [coordinateLaplacian_eq_of_eventuallyEq (hhf.filter_mono (nhds_le_nhdsSet hxS))]
    exact hfLap x (hSU hxS)
  · let w : ℕ → Space n → ℝ := fun j =>
      normalizedQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j))
    let v : ℕ → Space n → ℝ := fun j =>
      continuousDualError (u (σ j)) (c (σ j)) (ε (σ j)) T
    let χ : ContDiffBump (0 : Space n) := ⟨T / 32, 3 * T / 64, by positivity, by linarith⟩
    have hχs : tsupport (χ : Space n → ℝ) ⊆ closedBall (0 : Space n) (3 * T / 64) := by
      rw [χ.tsupport_eq]
    have hχs8 : tsupport (χ : Space n → ℝ) ⊆ ball (0 : Space n) (T / 8) :=
      hχs.trans (closedBall_subset_ball (by linarith))
    have hχs4 : tsupport (χ : Space n → ℝ) ⊆ ball (0 : Space n) (T / 4) :=
      hχs.trans (closedBall_subset_ball (by linarith))
    have hw (j : ℕ) : Continuous (w j) :=
      ((hLip (σ j)).continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const (ε (σ j))
    have hv (j : ℕ) : Continuous (v j) :=
      continuous_continuousDualError (hLip (σ j)).continuous _ _ hT
    have hstrict (j : ℕ) : StrictConvexOn ℝ univ (u (σ j)) := by
      let := hfinite (σ j)
      exact moment_strictConvexOn (hLip (σ j)) (hc (σ j)) (hV (σ j))
        (hK (σ j)).measurableSet (hKc (σ j)) (hpush (σ j))
    have hεσ : Tendsto (fun j => ε (σ j)) atTop (𝓝 0) := hεlim.comp hσ.tendsto_atTop
    have hsmall : ∀ᶠ j in atTop, ε (σ j) * M ≤ T ^ 2 / 16 := by
      apply (show Tendsto (fun j => ε (σ j) * M) atTop (𝓝 0) by
        simpa using hεσ.mul_const M).eventually_le_const
      positivity
    have hhalf : ∀ᶠ j in atTop, ε (σ j) ≤ 1 / 2 := hεσ.eventually_le_const (by norm_num)
    have hae : h =ᵐ[volume.restrict (closedBall (0 : Space n) (3 * T / 64))] (g : Space n → ℝ) := by
      apply (ae_restrict_iff' isClosed_closedBall.measurableSet).mpr
      filter_upwards [(ae_restrict_iff' isOpen_ball.measurableSet).mp hfg] with x hx
      intro hxS
      rw [hhf.self_of_nhdsSet hxS, hx (hSU hxS)]
    have hE : Tendsto (fun j => ∫ x, χ x * |w j x - h x|) atTop (𝓝 0) :=
      weighted_abs_integral_tendsto_zero_of_strong_cutoff_limit hw hχ₀.continuous hχ₀c
        (Lp.memLp g) χ.continuous χ.hasCompactSupport isClosed_closedBall.measurableSet hχs
        (fun x hx => hχ₀one x (closedBall_subset_closedBall (by linarith) hx)) hae hconv
    have hG : Tendsto (fun j => ∫ x, χ x * (w j x - v j x)) atTop (𝓝 0) := by
      have hG₀ := (moment_primal_dual_pairing_tendsto_zero_on_ball hn hLip hc hV hfinite hK hKc hpush
        hε hεlim hT hM hdensity hbound χ.contDiff χ.hasCompactSupport hχs8 (fun _ => χ.nonneg)).comp hσ.tendsto_atTop
      apply hG₀.congr'
      filter_upwards [hsmall] with j hj
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [w, v, Function.comp_apply]
        by_cases hx : x ∈ tsupport (χ : Space n → ℝ)
        · rw [continuousDualError_eq_dual (hLip (σ j)).continuous (hstrict j) (hε (σ j)) hT hj
            (hbound (σ j)) (hχs4 hx), mul_comm]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
    apply tendstoUniformlyOn_of_radial_primal_dual_sandwich hw hv hh.continuous
      χ.continuous χ.hasCompactSupport (fun _ => χ.nonneg) (r := T / 64) (s := T / 32) (R := T / 64)
      (by linarith) (by positivity) (fun x hx => χ.one_of_mem_closedBall hx) hE hG
      (e := fun j => ε (σ j) * (T / 32) ^ 2)
    · simpa using hεσ.mul_const ((T / 32) ^ 2)
    · filter_upwards [hsmall] with j hj
      intro x
      by_cases hx : x ∈ tsupport (χ : Space n → ℝ)
      · exact mul_nonneg χ.nonneg (sub_nonneg.mpr
          (continuousDualError_le_primal (hLip (σ j)).continuous (hstrict j) (hε (σ j)) hT hj
            (hbound (σ j)) (hχs4 hx)))
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    · intro t ht htR
      filter_upwards [hsmall, hhalf] with j hj hjhalf
      intro a ha
      let := hfinite (σ j)
      exact moment_radial_average_sandwich hn (hLip (σ j)) (hc (σ j)) (hV (σ j))
        (hK (σ j)) (hKc (σ j)) (hpush (σ j)) (hε (σ j)) hjhalf hT hj (hbound (σ j))
        (hdensity (σ j)) ht htR ha

end KLS
end
