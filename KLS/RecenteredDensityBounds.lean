import KLS.RecenteredQuadraticFlatness

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma weightedDataDensity_pos (d : NormalizedWeightedMomentData n 1 1) (x : Space n) :
    0 < weightedDataDensity d x := Real.exp_pos _

lemma weightedDataDensity_inner_lower
    (d₀ : NormalizedWeightedMomentData n 1 1) (hε : d₀.epsilon ≤ 1 / 2)
    {c : Space n} (hc : ‖c‖ ≤ 1 / 4) : 1 / 2 ≤ weightedDataDensity d₀ c := by
  have hb := d₀.density c (by rw [mem_closedBall_zero_iff]; linarith)
  change |weightedDataDensity d₀ c - 1| ≤ d₀.epsilon ^ 2 at hb
  have hp := d₀.epsilon_pos
  have hlo := (abs_le.mp hb).1
  nlinarith

theorem exists_recentered_density_calibration (hn : 0 < n)
    (d₀ : NormalizedWeightedMomentData n 1 1) (hε : d₀.epsilon ≤ 1 / 2)
    {c : Space n} (hc : ‖c‖ ≤ 1 / 4) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A.det = weightedDataDensity d₀ c ∧
      ‖matrixAction (A - 1)‖ ≤ d₀.epsilon ^ 2 ∧
      ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 2 ∧
      ‖matrixAction (inverseSqrtMatrix A)⁻¹‖ ≤ 2 := by
  let A := centeredDensityMatrix (⟨0, hn⟩ : Fin n) (weightedDataDensity d₀ c)
  have hA : A.PosDef := centeredDensityMatrix_posDef _ (weightedDataDensity_pos d₀ c)
  have hclose : ‖matrixAction (A - 1)‖ ≤ d₀.epsilon ^ 2 :=
    (norm_centeredDensityMatrix_increment_le _ _).trans (d₀.density c
      (by rw [mem_closedBall_zero_iff]; linarith))
  have hp := d₀.epsilon_pos
  have hs : d₀.epsilon ^ 2 ≤ 1 / 2 := by nlinarith
  refine ⟨A, hA, centeredDensityMatrix_det _ _, hclose, ?_, ?_⟩
  · exact (norm_inverseSqrtMatrix_action_le hA (sq_nonneg _) hs hclose).trans (by nlinarith)
  · exact (norm_inverse_inverseSqrtMatrix_action_le hA (sq_nonneg _) hclose).trans (by nlinarith)

lemma norm_quarter_matrix_displacement_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ‖matrixAction B‖ ≤ 2) (y : Space n) :
    ‖(1 / 4 : ℝ) • matrixAction B y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hb := (matrixAction B).le_opNorm y
  have hm := mul_le_mul_of_nonneg_right hB (norm_nonneg y)
  linarith

/-- A full two-point Holder modulus gives the normalized radial density
bound at every inner center after its actual central-density calibration. -/
theorem recentered_normalized_density_holder
    (d₀ : NormalizedWeightedMomentData n 1 1) (hε : d₀.epsilon ≤ 1 / 2)
    {α : ℝ} (hα : 0 < α)
    (hholder : ∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α)
    {c : Space n} {A : Matrix (Fin n) (Fin n) ℝ} (hdet : A.det = weightedDataDensity d₀ c)
    (hB : ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 2)
    (hc : ‖c‖ ≤ 1 / 4) :
    ∀ y ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ (c + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A) y) / A.det - 1| ≤
        (32 * d₀.epsilon) ^ 2 * ‖y‖ ^ α := by
  intro y hy
  have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using hy
  let x := c + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A) y
  have hnorm : ‖x - c‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    simpa only [x, add_sub_cancel_left] using norm_quarter_matrix_displacement_le hB y
  have hxhalf : ‖x - c‖ ≤ 1 / 2 := by linarith
  have hxunit : x ∈ closedBall (0 : Space n) 1 := by
    rw [mem_closedBall_zero_iff]
    exact recentered_half_ball_subset_unit hc hxhalf
  have hcunit : c ∈ closedBall (0 : Space n) 1 := by rw [mem_closedBall_zero_iff]; linarith
  have hfc := weightedDataDensity_pos d₀ c
  have hfclow := weightedDataDensity_inner_lower d₀ hε hc
  have hb := abs_relative_density_sub_one_le hfc (hholder x hxunit c hcunit)
  have hcoef : d₀.epsilon ^ 2 / weightedDataDensity d₀ c ≤ 2 * d₀.epsilon ^ 2 := by
    apply (div_le_iff₀ hfc).mpr
    nlinarith [sq_nonneg d₀.epsilon]
  have hpow : ‖x - c‖ ^ α ≤ ‖y‖ ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (by linarith [norm_nonneg y]) hα.le
  rw [hdet]
  change |weightedDataDensity d₀ x / weightedDataDensity d₀ c - 1| ≤ _
  calc
    _ ≤ (d₀.epsilon ^ 2 / weightedDataDensity d₀ c) * ‖x - c‖ ^ α := hb
    _ ≤ (2 * d₀.epsilon ^ 2) * ‖y‖ ^ α :=
      mul_le_mul hcoef hpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    _ ≤ (32 * d₀.epsilon) ^ 2 * ‖y‖ ^ α := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      nlinarith [sq_nonneg d₀.epsilon]

end KLS
end
