import KLS.CutoffC1Energy
import KLS.WeightedMomentEnergy

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual weighted normalized moment sequence has a genuine strongly L2
convergent subsequence after every fixed interior compact C1 localization.
The uniform energy bound is derived, and the finitely many large epsilon
terms are discarded explicitly. -/
theorem weighted_exists_strong_L2_subsequence_of_cutoff (hn : 0 < n)
    {u W V : ℕ → Space n → ℝ} {L : ℕ → ℝ≥0}
    (hLip : ∀ j, LipschitzWith (L j) (u j))
    (hu : ∀ j, ContDiff ℝ 1 (u j)) (hc : ∀ j, StrictConvexOn ℝ univ (u j))
    (hW : ∀ j, Continuous (W j)) (hV : ∀ j, Continuous (V j))
    {K : ℕ → Set (Space n)} (hK : ∀ j, IsClosed (K j)) (hKc : ∀ j, Convex ℝ (K j))
    (hpush : ∀ j, (potentialMeasure (W j)).map (gradient (u j)) = (potentialMeasure (V j)).restrict (K j))
    {c ε : ℕ → ℝ} {r R T M : ℝ}
    (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) (hR : 0 < R)
    (hrR : r < R) (hRT : R < T) (hM : 0 ≤ M)
    (hdensity : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |Real.exp (-W j x + V j (gradient (u j) x)) - 1| ≤ (ε j) ^ 2)
    (hbound : ∀ j x, x ∈ closedBall (0 : Space n) T →
      |normalizedQuadraticError (u j) 0 0 (c j) (ε j) x| ≤ M)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ closedBall (0 : Space n) r) :
    ∃ (g : Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ), StrictMono σ ∧
      Tendsto (fun j => eLpNorm
        ((fun x => χ x * normalizedQuadraticError (u (σ j)) 0 0 (c (σ j)) (ε (σ j)) x) -
          (g : Space n → ℝ)) 2 volume) atTop (𝓝 0) := by
  have hhalf : ∀ᶠ j in atTop, ε j ≤ 1 / 2 := hεlim.eventually_le_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hhalf
  let w (j : ℕ) := normalizedQuadraticError (u (j+N)) 0 0 (c (j+N)) (ε (j+N))
  let E := 32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
    2 * n * r ^ 2 * (∫ x, χ x ^ 2)
  have hw (j : ℕ) : ContDiff ℝ 1 (w j) :=
    contDiff_normalizedQuadraticError (hu (j+N)) _ _ _ _
  have hE : 0 ≤ E := by
    dsimp [E]
    exact add_nonneg
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))
  have hb (j : ℕ) (x : Space n) (hx : x ∈ tsupport χ) : |w j x| ≤ M :=
    hbound (j+N) x (closedBall_subset_closedBall (by linarith : r ≤ T) (hχs hx))
  have he (j : ℕ) : (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (w j) i x ^ 2) ≤ E := by
    exact weighted_normalizedQuadraticError_caccioppoli hn (hLip (j+N)) (hu (j+N))
      (hc (j+N)).convexOn (hW (j+N)) (hV (j+N))
      (hK (j+N)) (hKc (j+N)) (hpush (j+N)) hχ hχc 0 0 (c (j+N)) (hε (j+N))
      (hN (j+N) (by omega)) hR hrR hRT hχs (hdensity (j+N)) hM (hb j)
  obtain ⟨g, σ, hσ, hconv⟩ := exists_strong_L2_subsequence_of_cutoff_energy hw hχ hχc hM hE hχs hb he
  exact ⟨g, fun j => σ j + N, hσ.add_const N, hconv⟩

end KLS
end
