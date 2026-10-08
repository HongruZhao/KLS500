import KLS.ScaledUniformHessianContinuity

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- One actual perturbative weighted datum supplies the entire original-
coordinate quadratic family on its inner ball. All constants are uniform
over centers; no neighborhood initializer or coefficient field is assumed. -/
theorem weighted_exists_uniform_inner_quadratic_family (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ r β C Δ : ℝ, 0 < r ∧ r < 1 ∧ 0 ≤ β ∧ β < 1 ∧ 0 < C ∧ 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α) →
      ∃ H : Space n → Matrix (Fin n) (Fin n) ℝ,
        (∀ c ∈ closedBall (0 : Space n) (1 / 4),
          (H c).PosDef ∧ (H c).det = weightedDataDensity d₀ c) ∧
        (∀ c ∈ closedBall (0 : Space n) (1 / 4), ∀ (j : ℕ) (x : Space n),
          ‖x - c‖ ≤ r ^ j / 16 →
          |d₀.u x - centeredQuadratic (H c) c (gradient d₀.u c) (d₀.u c) x| ≤
            C * d₀.epsilon * β ^ j * r ^ (2 * j)) := by
  classical
  obtain ⟨ρ, β, C₀, Δ₀, hρ, hρsmall, hβhalf, hβone, hC₀, hΔ₀, hquad⟩ :=
    weighted_exists_limiting_quadratic hn hα
  let r := ρ / 2
  let Δ := min (1 / 2) (Δ₀ / 32)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrone : r < 1 := by dsimp [r]; linarith
  have hβ : 0 ≤ β := by linarith
  have hΔ : 0 < Δ := lt_min (by norm_num) (by positivity)
  refine ⟨r, β, 2 * C₀, Δ, hr, hrone, hβ, hβone, by positivity, hΔ, ?_⟩
  intro d₀ hd hholder
  have hε : d₀.epsilon ≤ 1 / 2 := hd.le.trans (min_le_left _ _)
  have hεsmall : 32 * d₀.epsilon < Δ₀ := by
    have hh := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mp (hd.trans_le (min_le_right _ _))
    linarith
  have hD : 0 ≤ 2 * C₀ * d₀.epsilon :=
    mul_nonneg (mul_nonneg (by norm_num) hC₀.le) d₀.epsilon_pos.le
  have hlocal (c : Space n) (hc : c ∈ closedBall (0 : Space n) (1 / 4)) :
      ∃ G : Matrix (Fin n) (Fin n) ℝ, G.PosDef ∧ G.det = weightedDataDensity d₀ c ∧
        ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ r ^ j / 16 →
          |d₀.u x - centeredQuadratic G c (gradient d₀.u c) (d₀.u c) x| ≤
            (2 * C₀) * d₀.epsilon * β ^ j * r ^ (2 * j) := by
    obtain ⟨A, d, hA, hdetA, _, hBinv, hdε, _, hdu, _, hdholder⟩ :=
      exists_uniform_recentered_weighted_data hn d₀ hε hα hholder c
        (by simpa only [mem_closedBall_zero_iff] using hc)
    have hdsmall : d.epsilon < Δ₀ := by rw [hdε]; exact hεsmall
    obtain ⟨J, q, b, hJ, hdetJ, hb⟩ := hquad d hdsmall hdholder
    let G := (inverseSqrtMatrix A)⁻¹.transpose * J * (inverseSqrtMatrix A)⁻¹
    obtain ⟨hG, hdetG⟩ := inverseSqrt_pullback_posDef_det hA hJ hdetJ
    let p := c + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A)⁻¹.transpose q
    let a := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c + (1 / 4 : ℝ) ^ 2 * b
    have hboriginal : ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ r ^ j / 16 →
        |d₀.u x - centeredQuadratic G c p a x| ≤
          (2 * C₀) * d₀.epsilon * β ^ j * r ^ (2 * j) := by
      have hh := whitened_quadratic_approximation_on_ball c c
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) hA hBinv hdu hb
      intro j x hx
      have he := hh j x hx
      rw [hdε] at he
      exact he.trans_eq (by ring)
    have hbscaled : ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ (1 / 8 : ℝ) * r ^ j / 2 →
        |d₀.u x - centeredQuadratic G c p a x| ≤
          (2 * C₀ * d₀.epsilon) * β ^ j * r ^ (2 * j) := by
      intro j x hx
      exact hboriginal j x (hx.trans_eq (by ring))
    obtain ⟨ha, hp⟩ := value_gradient_of_scaled_geometric_taylor hG.posSemidef hD
      (by norm_num : (0 : ℝ) < 1 / 8) hr hrone hβ hβone hbscaled
    rw [ha, hp] at hboriginal
    exact ⟨G, hG, hdetG.trans hdetA, hboriginal⟩
  let H : Space n → Matrix (Fin n) (Fin n) ℝ := fun c =>
    if hc : c ∈ closedBall (0 : Space n) (1 / 4) then Classical.choose (hlocal c hc) else 1
  have hH (c : Space n) (hc : c ∈ closedBall (0 : Space n) (1 / 4)) :
      (H c).PosDef ∧ (H c).det = weightedDataDensity d₀ c ∧
        ∀ (j : ℕ) (x : Space n), ‖x - c‖ ≤ r ^ j / 16 →
          |d₀.u x - centeredQuadratic (H c) c (gradient d₀.u c) (d₀.u c) x| ≤
            (2 * C₀) * d₀.epsilon * β ^ j * r ^ (2 * j) := by
    simpa only [H, dite_eq_left hc] using Classical.choose_spec (hlocal c hc)
  exact ⟨H, fun c hc => ⟨(hH c hc).1, (hH c hc).2.1⟩, fun c hc => (hH c hc).2.2⟩

end KLS
end
