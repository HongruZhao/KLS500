import KLS.WeightedHarmonicApproximation
import KLS.HarmonicCorrectionCoefficientBounds
import KLS.ClassicalViscosityHarmonic

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual one-step improvement of flatness for the weighted weak moment
potential, with a positive-definite determinant-one approximating Hessian.
The radius, epsilon threshold, and coefficient bound are uniform over the data. -/
theorem weighted_one_step_improvement_with_coefficients (hn : 0 < n)
    {T M θ : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hθ : 0 < θ) :
    ∃ ρ δ Q : ℝ, 0 < ρ ∧ ρ ≤ T / 512 ∧ 0 < δ ∧ 0 < Q ∧
      ∀ d : NormalizedWeightedMomentData n T M, d.epsilon < δ →
        ∃ (A : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a : ℝ),
          A.PosDef ∧ A.det = 1 ∧
          ‖matrixAction (A - 1)‖ ≤ Q * d.epsilon ∧
          ‖p‖ ≤ Q * d.epsilon ∧ |a - d.c| ≤ Q * d.epsilon ∧
          ∀ x ∈ closedBall (0 : Space n) ρ,
            |d.u x - centeredQuadratic A 0 p a x| ≤ θ * d.epsilon * ρ ^ 2 := by
  let R := T / 64
  let B := M ^ 2
  let C := nonlinearComparisonConstant n
  let H := harmonicTaylorHessianBound n R B
  let G := (n : ℝ) * Real.sqrt ((120 + 8 * n) * B / R ^ 2)
  let Q := (H + 4 * C * H ^ 2) + G + M + 1
  let η := θ / 4
  let ρ := harmonicApproximationRadius n R B η
  have hR : 0 < R := by dsimp [R]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := harmonicApproximationRadius_pos hR hη
  have hρR : ρ ≤ R / 8 := harmonicApproximationRadius_le R B η
  have hC : 0 < C := by dsimp [C]; linarith [nonlinearComparisonConstant_gt_two n]
  have hH : 0 < H := harmonicTaylorHessianBound_pos n R B
  obtain ⟨δ₀, hδ₀, ha⟩ := weighted_harmonic_approximation_threshold hn hT hM
    (show 0 < θ * ρ ^ 2 / 2 by positivity)
  let δ₁ := (1 / (2 * C)) / (2 * H)
  let δ₂ := η / (2 * C * H ^ 2)
  let δ := min δ₀ (min δ₁ (min δ₂ 1))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by dsimp [δ₁]; positivity)
    (lt_min (by dsimp [δ₂]; positivity) (by norm_num)))
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hHC : 0 ≤ H + 4 * C * H ^ 2 := by positivity
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hQH : H + 4 * C * H ^ 2 ≤ Q := by dsimp [Q]; linarith
  have hQG : G ≤ Q := by dsimp [Q]; linarith
  have hQM : M ≤ Q := by dsimp [Q]; linarith
  refine ⟨ρ, δ, Q, hρ, ?_, hδ, hQ, ?_⟩
  · dsimp [R] at hρR
    linarith
  · intro d hd
    have hd₀ : d.epsilon < δ₀ := hd.trans_le (min_le_left _ _)
    have hd₁ : d.epsilon ≤ δ₁ := hd.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hd₂ : d.epsilon ≤ δ₂ := hd.le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hdone : d.epsilon ≤ 1 := hd.le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hsmall : 2 * H * d.epsilon ≤ 1 / (2 * C) := by
      have hh := (le_div_iff₀ (show 0 < 2 * H by positivity)).mp hd₁
      linarith
    have hcorrection : 2 * C * H ^ 2 * d.epsilon ≤ η := by
      have hh := (le_div_iff₀ (show 0 < 2 * C * H ^ 2 by positivity)).mp hd₂
      linarith
    obtain ⟨h, hh, hLap, hb, herror⟩ := ha d hd₀
    have hhv := isViscosityHarmonicOn_of_contDiff (hh.of_le (by simp)) hLap
    have hball : closedBall (0 : Space n) R ⊆ ball (0 : Space n) (T / 32) :=
      closedBall_subset_ball (by dsimp [R]; linarith)
    have hbsq : ∀ x ∈ closedBall (0 : Space n) R, h x ^ 2 ≤ B := by
      intro x hx
      have hhx := hb x hx
      have hp := (abs_le.mp hhx).1
      have hm := (abs_le.mp hhx).2
      dsimp [B]
      nlinarith
    obtain ⟨A, hA, hdet, hAinc, hq⟩ := hhv.exists_controlled_det_one_quadratic hn isOpen_ball hR hη
      hball hbsq d.epsilon_pos hdone hsmall hcorrection 0 d.c
    refine ⟨A, d.epsilon • gradient h 0, d.c + d.epsilon * h 0, hA, hdet, ?_, ?_, ?_, ?_⟩
    · exact hAinc.trans (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hQH d.epsilon_pos.le)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos d.epsilon_pos]
      calc
        _ ≤ d.epsilon * G := mul_le_mul_of_nonneg_left
          (hhv.norm_taylor_gradient_le isOpen_ball hR hball hbsq) d.epsilon_pos.le
        _ ≤ Q * d.epsilon := by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hQG d.epsilon_pos.le
    · rw [add_sub_cancel_left, abs_mul, abs_of_pos d.epsilon_pos]
      have hb0 := hb 0 (mem_closedBall_self hR.le)
      calc
        _ ≤ d.epsilon * M := mul_le_mul_of_nonneg_left hb0 d.epsilon_pos.le
        _ ≤ Q * d.epsilon := by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hQM d.epsilon_pos.le
    ·
      intro x hx
      have hxR : x ∈ closedBall (0 : Space n) R :=
        closedBall_subset_closedBall (hρR.trans (by linarith)) hx
      have hn : ‖x‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hx
      have hnorm : ‖x‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg x]
      have hfirst : |d.u x - (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c x + d.epsilon * h x)| ≤
          d.epsilon * (θ * ρ ^ 2 / 2) := by
        rw [normalizedQuadraticError_reconstruction d.u 0 0 d.c d.epsilon_pos.ne' x]
        have he : centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c x +
            d.epsilon * normalizedQuadraticError d.u 0 0 d.c d.epsilon x -
            (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c x + d.epsilon * h x) =
            d.epsilon * (normalizedQuadraticError d.u 0 0 d.c d.epsilon x - h x) := by ring
        rw [he, abs_mul, abs_of_pos d.epsilon_pos]
        exact mul_le_mul_of_nonneg_left (herror x hxR) d.epsilon_pos.le
      have hsecond := hq x hx
      simp only [zero_add, sub_zero] at hsecond
      have htriangle := abs_sub_le (d.u x)
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c x + d.epsilon * h x)
        (centeredQuadratic A 0 (d.epsilon • gradient h 0) (d.c + d.epsilon * h 0) x)
      have hsq := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * d.epsilon * η from mul_nonneg (mul_nonneg (by norm_num) d.epsilon_pos.le) hη.le)
      dsimp only [η] at hsecond hsq
      linarith


/-- Unbundled form with the actual source, target, pushforward, density,
and coefficient estimates all visible in the statement. -/
theorem weighted_exists_improved_det_one_quadratic_with_coefficients (hn : 0 < n)
    {T M θ : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hθ : 0 < θ) :
    ∃ ρ δ Q : ℝ, 0 < ρ ∧ ρ ≤ T / 512 ∧ 0 < δ ∧ 0 < Q ∧
      ∀ (u W V : Space n → ℝ) (L : ℝ≥0) (K : Set (Space n)) (c ε : ℝ),
        LipschitzWith L u → ContDiff ℝ 1 u → StrictConvexOn ℝ univ u →
        Continuous W → Continuous V → IsClosed K → Convex ℝ K →
        (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K →
        0 < ε → ε < δ →
        (∀ x ∈ closedBall (0 : Space n) T, |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2) →
        (∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M) →
        ∃ (A : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a : ℝ),
          A.PosDef ∧ A.det = 1 ∧ ‖matrixAction (A - 1)‖ ≤ Q * ε ∧
          ‖p‖ ≤ Q * ε ∧ |a - c| ≤ Q * ε ∧
          ∀ x ∈ closedBall (0 : Space n) ρ,
            |u x - centeredQuadratic A 0 p a x| ≤ θ * ε * ρ ^ 2 := by
  obtain ⟨ρ, δ, Q, hρ, hρT, hδ, hQ, ha⟩ :=
    weighted_one_step_improvement_with_coefficients hn hT hM hθ
  refine ⟨ρ, δ, Q, hρ, hρT, hδ, hQ, ?_⟩
  intro u W V L K c ε hLip hu hc hW hV hK hKc hpush hε hsmall hdensity hbound
  exact ha ⟨u, W, V, L, K, c, ε, hLip, hu, hc, hW, hV, hK, hKc, hpush,
    hε, hdensity, hbound⟩ hsmall

end KLS
end
