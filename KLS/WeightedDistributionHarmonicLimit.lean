import KLS.WeightedFirstOrderWeakBound

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Every fixed inner compact C2 test has vanishing normalized Laplacian
pairing along the weighted moment sequence. No convergence of the sequence,
second derivatives of its potentials, or energy estimate is assumed. -/
theorem weighted_normalized_laplacian_pairing_tendsto_zero (hn : 0 < n)
    {u W V : ℕ → Space n → ℝ} {L : ℕ → ℝ≥0}
    (hLip : ∀ j, LipschitzWith (L j) (u j))
    (hu : ∀ j, ContDiff ℝ 1 (u j)) (hc : ∀ j, StrictConvexOn ℝ univ (u j))
    (hW : ∀ j, Continuous (W j)) (hV : ∀ j, Continuous (V j))
    {K : ℕ → Set (Space n)} (hK : ∀ j, IsClosed (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hpush : ∀ j, (potentialMeasure (W j)).map (gradient (u j)) = (potentialMeasure (V j)).restrict (K j))
    {ψ χ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {c ε : ℕ → ℝ} {R r S T M : ℝ}
    (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) (hR : 0 < R)
    (hRr : R ≤ r) (hrS : r < S) (hST : S < T) (hM : 0 ≤ M)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχs : tsupport χ ⊆ closedBall (0 : Space n) r)
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |Real.exp (-W j x + V j (gradient (u j) x)) - 1| ≤ (ε j) ^ 2)
    (hbound : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |normalizedQuadraticError (u j) 0 0 (c j) (ε j) x| ≤ M) :
    Tendsto (fun j => ∫ x, normalizedQuadraticError (u j) 0 0 (c j) (ε j) x *
      coordinateLaplacian ψ x) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  obtain ⟨M₂, hM₂, hHbound⟩ := exists_bound_coordinateHessian_of_hasCompactSupport hψ hψc
  let C := (n : ℝ) ^ 2 * M₂ *
    (32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
      2 * n * r ^ 2 * (∫ x, χ x ^ 2)) + |B| * (∫ x, χ x ^ 2)
  have hhalf : ∀ᶠ j in atTop, ε j ≤ 1 / 2 := hεlim.eventually_le_const (by norm_num)
  have hsmall : ∀ᶠ j in atTop, ε j * M ≤ R ^ 2 / 16 := by
    apply (show Tendsto (fun j => ε j * M) atTop (𝓝 0) by simpa using hεlim.mul_const M).eventually_le_const
    positivity
  apply squeeze_zero_norm' (a := fun j => ε j * C)
  · filter_upwards [hhalf, hsmall] with j hjhalf hjsmall
    exact weighted_normalized_laplacian_pairing_bound hn (hLip j) (hu j) (hc j) (hW j) (hV j) (hK j)
      (hKc j) (hpush j) hψ hψc hχ hχc (hε j) hjhalf hR hRr hrS hST hjsmall hM
      (abs_nonneg B) hM₂ hψs hχs hχone (hdensity j) (hbound j)
      (fun x => (hB x).trans (le_abs_self B)) hHbound
  · simpa using hεlim.mul_const C


/-- A canonical smooth cutoff removes all cutoff data from the endpoint.
On the inner one-eighth ball, every actual compact C2 Laplace test vanishes
asymptotically under the actual weighted weak transport and normalized-flatness hypotheses. -/
theorem weighted_normalized_laplacian_pairing_tendsto_zero_on_ball (hn : 0 < n)
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
      |normalizedQuadraticError (u j) 0 0 (c j) (ε j) x| ≤ M)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (T / 8)) :
    Tendsto (fun j => ∫ x, normalizedQuadraticError (u j) 0 0 (c j) (ε j) x *
      coordinateLaplacian ψ x) atTop (𝓝 0) := by
  let χ : ContDiffBump (0 : Space n) := ⟨T / 2, 3 * T / 4, by positivity, by linarith⟩
  apply weighted_normalized_laplacian_pairing_tendsto_zero hn hLip hu hc hW hV hK hKc hpush
    hψ hψc χ.contDiff χ.hasCompactSupport hε hεlim (R := T / 2) (r := 3 * T / 4)
    (S := 7 * T / 8) (T := T) (M := M) (by positivity) (by linarith) (by linarith)
    (by linarith) hM
  · simpa only [div_div, show (2 : ℝ) * 4 = 8 by norm_num] using hψs
  · rw [χ.tsupport_eq]
  · intro x hx
    exact χ.one_of_mem_closedBall hx
  · exact hdensity
  · exact hbound

end KLS
end
