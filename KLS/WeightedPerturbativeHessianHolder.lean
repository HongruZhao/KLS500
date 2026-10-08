import KLS.UniformHessianHolder

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual coordinate Hessian of one perturbative weighted moment
potential is Holder, with an exponent uniform over the normalized data.
The constant may depend on the datum's existing Lipschitz constant. -/
theorem weighted_perturbative_hessian_holder (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ γ : ℝ, 0 < Δ ∧ 0 < γ ∧ γ ≤ 1 ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α) →
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ c ∈ closedBall (0 : Space n) (1 / 4), ∀ d ∈ closedBall (0 : Space n) (1 / 4),
          ‖coordinateHessian d₀.u c - coordinateHessian d₀.u d‖ ≤ M * ‖c - d‖ ^ γ := by
  obtain ⟨r, β, C, Δ, hr, hrone, hβ, hβone, hC, hΔ, hfamily⟩ :=
    weighted_exists_uniform_inner_quadratic_family hn hα
  let θ := (1 + β) / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθone : θ < 1 := by dsimp [θ]; linarith
  have hβθ : β ≤ θ := by dsimp [θ]; linarith
  have hs : 0 < θ * r ^ 2 := by positivity
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hsθ : θ * r ^ 2 ≤ θ := (mul_lt_of_lt_one_right hθ hr2).le
  obtain ⟨γ, hγ, hγone, hscale⟩ := geometric_holder_exponent hs
    (hsθ.trans_lt hθone) hθ hθone hsθ
  refine ⟨Δ, γ, hΔ, hγ, hγone, ?_⟩
  intro d₀ hd hholder
  obtain ⟨H, hH, hb⟩ := hfamily d₀ hd hholder
  have hu := d₀.contDiff.differentiable (by norm_num)
  have hD : 0 ≤ C * d₀.epsilon := mul_nonneg hC.le d₀.epsilon_pos.le
  have hsym (c : Space n) (hc : c ∈ closedBall (0 : Space n) (1 / 4)) : (H c).IsSymm :=
    (hH c hc).1.isHermitian.isSymm
  have hbound : ∀ c ∈ closedBall (0 : Space n) (1 / 4), ∀ (j : ℕ) (x : Space n),
      ‖x - c‖ ≤ (1 / 8 : ℝ) * r ^ j / 2 →
      |d₀.u x - centeredQuadratic (H c) c (gradient d₀.u c) (d₀.u c) x| ≤
        (C * d₀.epsilon) * β ^ j * r ^ (2 * j) := by
    intro c hc j x hx
    exact hb c hc j x (hx.trans_eq (by ring))
  have heq (c : Space n) (hc : c ∈ closedBall (0 : Space n) (1 / 4)) :
      coordinateHessian d₀.u c = H c := by
    exact coordinateHessian_eq_of_hasFDerivAt_gradient (hsym c hc)
      (hasFDerivAt_gradient_of_scaled_geometric_taylor hu d₀.strictConvex.convexOn
        (hsym c hc) hD (by norm_num : (0 : ℝ) < 1 / 8) hr hrone hβ hβone (hbound c hc))
  refine ⟨96 * (C * d₀.epsilon + d₀.L) / (1 / 8 : ℝ) ^ 2 / θ, by positivity, ?_⟩
  intro c hc d hd
  rw [heq c hc, heq d hd]
  apply hessian_holder_of_uniform_scaled_geometric_taylor d₀.lipschitz hsym hD
    (by norm_num : (0 : ℝ) < 1 / 8) hr hrone hβ hβθ hθ hθone hγ hscale hbound hc hd
  have hcn : ‖c‖ ≤ 1 / 4 := by simpa only [mem_closedBall_zero_iff] using hc
  have hdn : ‖d‖ ≤ 1 / 4 := by simpa only [mem_closedBall_zero_iff] using hd
  exact (norm_sub_le c d).trans (by linarith)

/-- A single threshold gives local C2 regularity, the classical nonlinear
equation, and a Holder modulus of the actual Hessian. -/
theorem weighted_perturbative_c2_holder_regularity (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ γ : ℝ, 0 < Δ ∧ 0 < γ ∧ γ ≤ 1 ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α) →
      ContDiffOn ℝ 2 d₀.u (ball (0 : Space n) (1 / 4)) ∧
      (∀ c ∈ ball (0 : Space n) (1 / 4), (coordinateHessian d₀.u c).PosDef ∧
        (coordinateHessian d₀.u c).det = weightedDataDensity d₀ c) ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ c ∈ closedBall (0 : Space n) (1 / 4), ∀ d ∈ closedBall (0 : Space n) (1 / 4),
          ‖coordinateHessian d₀.u c - coordinateHessian d₀.u d‖ ≤ M * ‖c - d‖ ^ γ := by
  obtain ⟨Δ₁, hΔ₁, hC2⟩ := weighted_perturbative_c2_regularity hn hα
  obtain ⟨Δ₂, γ, hΔ₂, hγ, hγone, hHol⟩ := weighted_perturbative_hessian_holder hn hα
  refine ⟨min Δ₁ Δ₂, γ, lt_min hΔ₁ hΔ₂, hγ, hγone, ?_⟩
  intro d₀ hd hholder
  obtain ⟨hreg, hMA⟩ := hC2 d₀ (hd.trans_le (min_le_left _ _)) hholder
  exact ⟨hreg, hMA, hHol d₀ (hd.trans_le (min_le_right _ _)) hholder⟩

end KLS
end
