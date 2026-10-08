import KLS.MomentStrongL2Compactness

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma laplacian_pairing_zero_of_strong_cutoff_limit
    {w : ℕ → Space n → ℝ} {χ ψ : Space n → ℝ} {g : Space n → ℝ}
    (hw : ∀ j, Continuous (w j)) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hg : MemLp g 2 volume) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hχone : ∀ x ∈ tsupport ψ, χ x = 1)
    (hconv : Tendsto (fun j => eLpNorm ((fun x => χ x * w j x) - g) 2 volume) atTop (𝓝 0))
    (hzero : Tendsto (fun j => ∫ x, w j x * coordinateLaplacian ψ x) atTop (𝓝 0)) :
    (∫ x, g x * coordinateLaplacian ψ x) = 0 := by
  have hb : MemLp (coordinateLaplacian ψ) 2 volume :=
    (continuous_coordinateLaplacian hψ).memLp_of_hasCompactSupport
      (hψc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordinateLaplacian_subset ψ))
  have hf (j : ℕ) : MemLp (fun x => χ x * w j x) 2 volume :=
    (hχ.mul (hw j)).memLp_of_hasCompactSupport hχc.mul_right
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hf hg hb hconv
  have hid (j : ℕ) : (∫ x, coordinateLaplacian ψ x * (χ x * w j x)) =
      ∫ x, w j x * coordinateLaplacian ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport (coordinateLaplacian ψ)
      · rw [hχone x (tsupport_coordinateLaplacian_subset ψ hx), one_mul, mul_comm]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  simp_rw [hid] at ht
  have hz := tendsto_nhds_unique ht hzero
  simpa only [mul_comm] using hz

/-- The actual L2 subsequence constructed from the original moment hypotheses
has a distribution-harmonic limit on the inner ball. -/
theorem moment_exists_strong_L2_distribution_harmonic_subsequence (hn : 0 < n)
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
  obtain ⟨g, σ, hσ, hconv⟩ := moment_exists_strong_L2_subsequence_of_cutoff hn
    hLip hc hV hfinite hK hKc hpush hε hεlim (R := T / 2) (r := T / 4) (T := T)
    (by positivity) (by linarith) (by linarith) hM hdensity hbound χ.contDiff χ.hasCompactSupport
    (by rw [χ.tsupport_eq])
  refine ⟨χ, g, σ, χ.contDiff, χ.hasCompactSupport, fun _ hx => χ.one_of_mem_closedBall hx,
    hσ, hconv, ?_⟩
  intro ψ hψ hψc hψs
  apply laplacian_pairing_zero_of_strong_cutoff_limit
    (fun j => ((hLip (σ j)).continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const (ε (σ j)))
    χ.continuous χ.hasCompactSupport (Lp.memLp g) hψ hψc
    (fun _ hx => χ.one_of_mem_closedBall (ball_subset_closedBall (hψs hx))) hconv
  exact (moment_normalized_laplacian_pairing_tendsto_zero_on_ball hn hLip hc hV hfinite hK hKc hpush
    hε hεlim hT hM hdensity hbound hψ hψc (hψs.trans ball_subset_closedBall)).comp hσ.tendsto_atTop

end KLS
end
