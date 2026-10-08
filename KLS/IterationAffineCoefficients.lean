import KLS.WeightedIterationHessianLimit

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual accumulated slope in the original normalized coordinates. -/
def iterationSlope {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1))) : ℕ → Space n
  | 0 => 0
  | j + 1 => iterationSlope s links j + (ρ / 2) ^ j •
      matrixAction ((s j).frame⁻¹.transpose) (links j).p

/-- The actual accumulated polynomial constant, including the initial
quadratic constant and subtracting each current normalized constant. -/
def iterationConstant {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1))) : ℕ → ℝ
  | 0 => d₀.c
  | j + 1 => iterationConstant s links j + (ρ / 2) ^ (2 * j) * ((links j).a - (s j).data.c)

lemma norm_iterationSlope_increment_le
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hinv : ∀ j, ‖matrixAction ((s j).frame⁻¹)‖ ≤ 2) (hρ : 0 ≤ ρ) (j : ℕ) :
    ‖iterationSlope s links (j + 1) - iterationSlope s links j‖ ≤
      (2 * Q * d₀.epsilon) * ((ρ / 2) * β) ^ j := by
  rw [iterationSlope, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by positivity) j)]
  have hb := (matrixAction ((s j).frame⁻¹.transpose)).le_opNorm (links j).p
  rw [norm_matrixAction_transpose] at hb
  have hprod : ‖matrixAction ((s j).frame⁻¹.transpose) (links j).p‖ ≤ 2 * (Q * (s j).data.epsilon) :=
    hb.trans (mul_le_mul (hinv j) (links j).slope_increment (norm_nonneg _) (by norm_num))
  have hh := mul_le_mul_of_nonneg_left hprod (pow_nonneg (by positivity : 0 ≤ ρ / 2) j)
  rw [(s j).epsilon_eq] at hh
  convert hh using 1
  rw [mul_pow]
  ring

lemma abs_iterationConstant_increment_le
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1))) (hρ : 0 ≤ ρ) (j : ℕ) :
    |iterationConstant s links (j + 1) - iterationConstant s links j| ≤
      (Q * d₀.epsilon) * ((ρ / 2) ^ 2 * β) ^ j := by
  rw [iterationConstant, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (pow_nonneg (by positivity) (2 * j))]
  have hh := mul_le_mul_of_nonneg_left (links j).constant_increment
    (pow_nonneg (by positivity : 0 ≤ ρ / 2) (2 * j))
  rw [(s j).epsilon_eq] at hh
  convert hh using 1
  rw [mul_pow, ← pow_mul]
  ring

lemma exists_limit_of_geometric_increment {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {C γ : ℝ} (hγ : γ < 1)
    (hf : ∀ j, ‖f (j + 1) - f j‖ ≤ C * γ ^ j) :
    ∃ a : E, Tendsto f atTop (𝓝 a) ∧ ∀ j, ‖f j - a‖ ≤ C * γ ^ j / (1 - γ) := by
  have hd (j : ℕ) : dist (f j) (f (j + 1)) ≤ C * γ ^ j := by
    rw [dist_eq_norm, norm_sub_rev]
    exact hf j
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric γ C hγ hd)
  exact ⟨a, ha, fun j => by simpa only [dist_eq_norm] using
    dist_le_of_le_geometric_of_tendsto γ C hγ hd ha j⟩

/-- The slope and constant of the original-coordinate approximating
polynomials converge with the correct extra spatial powers in their tails. -/
theorem iteration_affine_coefficients_limits
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hinv : ∀ j, ‖matrixAction ((s j).frame⁻¹)‖ ≤ 2)
    (hρ : 0 ≤ ρ) (hρsmall : ρ / 2 ≤ 1) (hβ : 0 ≤ β) (hβone : β < 1) :
    ∃ (p : Space n) (a : ℝ),
      Tendsto (iterationSlope s links) atTop (𝓝 p) ∧
      Tendsto (iterationConstant s links) atTop (𝓝 a) ∧
      (∀ j, ‖iterationSlope s links j - p‖ ≤
        (2 * Q * d₀.epsilon) * ((ρ / 2) * β) ^ j / (1 - (ρ / 2) * β)) ∧
      (∀ j, |iterationConstant s links j - a| ≤
        (Q * d₀.epsilon) * ((ρ / 2) ^ 2 * β) ^ j / (1 - (ρ / 2) ^ 2 * β)) := by
  have hp : (ρ / 2) * β < 1 := (mul_le_of_le_one_left hβ hρsmall).trans_lt hβone
  have hs : (ρ / 2) ^ 2 ≤ 1 := by nlinarith
  have hc : (ρ / 2) ^ 2 * β < 1 := (mul_le_of_le_one_left hβ hs).trans_lt hβone
  obtain ⟨p, hpconv, hptail⟩ := exists_limit_of_geometric_increment hp
    (norm_iterationSlope_increment_le s links hinv hρ)
  obtain ⟨a, haconv, hatail⟩ := exists_limit_of_geometric_increment
    (f := iterationConstant s links) (C := Q * d₀.epsilon) hc
    (fun j => by simpa only [Real.norm_eq_abs] using abs_iterationConstant_increment_le s links hρ j)
  exact ⟨p, a, hpconv, haconv, hptail, fun j => by simpa only [Real.norm_eq_abs] using hatail j⟩

end KLS
end
