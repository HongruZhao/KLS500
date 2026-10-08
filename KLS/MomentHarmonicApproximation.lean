import KLS.UniformApproximationCompactness

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS

/-- Original weak moment data at a fixed outer radius and flatness bound.
Every field is a hypothesis of the unbundled compactness theorem. -/
structure NormalizedMomentData (n : ℕ) (T M : ℝ) where
  u : Space n → ℝ
  V : Space n → ℝ
  L : ℝ≥0
  K : Set (Space n)
  c : ℝ
  epsilon : ℝ
  lipschitz : LipschitzWith L u
  convex : ConvexOn ℝ univ u
  continuous_target : Continuous V
  finite : IsFiniteMeasure (potentialMeasure u)
  closed_target : IsClosed K
  convex_target : Convex ℝ K
  pushforward : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K
  epsilon_pos : 0 < epsilon
  density : ∀ x ∈ closedBall (0 : Space n) T,
    |Real.exp (-u x + V (gradient u x)) - 1| ≤ epsilon ^ 2
  bound : ∀ x ∈ closedBall (0 : Space n) T,
    |normalizedQuadraticError u 0 0 c epsilon x| ≤ M

variable {n : ℕ}

/-- The harmonic approximation threshold depends only on dimension, the
outer radius, the normalized size bound, and the requested uniform error. -/
theorem moment_harmonic_approximation_threshold (hn : 0 < n)
    {T M η : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : NormalizedMomentData n T M, d.epsilon < δ →
      ∃ h : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧
        (∀ x ∈ ball (0 : Space n) (T / 32), coordinateLaplacian h x = 0) ∧
        (∀ x ∈ closedBall (0 : Space n) (T / 64), |h x| ≤ M) ∧
        ∀ x ∈ closedBall (0 : Space n) (T / 64),
          |normalizedQuadraticError d.u 0 0 d.c d.epsilon x - h x| ≤ η := by
  let P : (Space n → ℝ) → Prop := fun h => ContDiff ℝ (⊤ : ℕ∞) h ∧
    (∀ x ∈ ball (0 : Space n) (T / 32), coordinateLaplacian h x = 0) ∧
    (∀ x ∈ closedBall (0 : Space n) (T / 64), |h x| ≤ M)
  have hcompact : ∀ d : ℕ → NormalizedMomentData n T M,
      Tendsto (fun j => (d j).epsilon) atTop (𝓝 0) →
      ∃ (h : Space n → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧ P h ∧
        TendstoUniformlyOn (fun j => normalizedQuadraticError
          (d (σ j)).u 0 0 (d (σ j)).c (d (σ j)).epsilon) h atTop (closedBall (0 : Space n) (T / 64)) := by
    intro d hlim
    obtain ⟨h, σ, hσ, hh, hLap, hconv, hbound⟩ := moment_exists_bounded_uniform_harmonic_subsequence hn
      (fun j => (d j).lipschitz) (fun j => (d j).convex) (fun j => (d j).continuous_target)
      (fun j => (d j).finite) (fun j => (d j).closed_target) (fun j => (d j).convex_target)
      (fun j => (d j).pushforward) (fun j => (d j).epsilon_pos) hlim hT hM
      (fun j => (d j).density) (fun j => (d j).bound)
    exact ⟨h, σ, hσ, ⟨hh, hLap, hbound⟩, hconv⟩
  obtain ⟨δ, hδ, ha⟩ := exists_uniform_approximation_threshold
    (fun d : NormalizedMomentData n T M => d.epsilon)
    (fun d => normalizedQuadraticError d.u 0 0 d.c d.epsilon)
    (closedBall (0 : Space n) (T / 64)) P (fun d => d.epsilon_pos) hcompact hη
  refine ⟨δ, hδ, ?_⟩
  intro d hd
  obtain ⟨h, hh, herror⟩ := ha d hd
  exact ⟨h, hh.1, hh.2.1, hh.2.2, herror⟩

/-- Unbundled original-data form: the smallness threshold is uniform over
all Lipschitz constants, potentials, target sets, and quadratic constants. -/
theorem moment_exists_harmonic_approximation (hn : 0 < n)
    {T M η : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u V : Space n → ℝ) (L : ℝ≥0) (K : Set (Space n)) (c ε : ℝ),
      LipschitzWith L u → ConvexOn ℝ univ u → Continuous V → IsFiniteMeasure (potentialMeasure u) →
      IsClosed K → Convex ℝ K →
      MomentMap.gradientPushforward u = (potentialMeasure V).restrict K → 0 < ε → ε < δ →
      (∀ x ∈ closedBall (0 : Space n) T, |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2) →
      (∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M) →
      ∃ h : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧
        (∀ x ∈ ball (0 : Space n) (T / 32), coordinateLaplacian h x = 0) ∧
        (∀ x ∈ closedBall (0 : Space n) (T / 64), |h x| ≤ M) ∧
        ∀ x ∈ closedBall (0 : Space n) (T / 64), |normalizedQuadraticError u 0 0 c ε x - h x| ≤ η := by
  obtain ⟨δ, hδ, ha⟩ := moment_harmonic_approximation_threshold hn hT hM hη
  refine ⟨δ, hδ, ?_⟩
  intro u V L K c ε hLip hc hV hfinite hK hKc hpush hε hsmall hdensity hbound
  exact ha ⟨u, V, L, K, c, ε, hLip, hc, hV, hfinite, hK, hKc, hpush, hε, hdensity, hbound⟩ hsmall

end KLS
end
