import KLS.PositiveMatrixLimit
import KLS.RegularMomentMapQuadratic

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual original-coordinate Hessians of a proved weighted iteration
converge to a positive-definite determinant-one matrix, with an explicit
geometric operator-norm tail. This is a coefficient limit, not yet a claim
that the original potential is twice differentiable. -/
theorem weighted_iteration_hessian_limit
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (hlinks : ∀ j, Nonempty (WeightedIterationLink (s j) (s (j + 1))))
    (hinv : ∀ j, ‖matrixAction ((s j).frame⁻¹)‖ ≤ 2) (hβone : β < 1) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, H.PosDef ∧ H.det = 1 ∧
      Tendsto (fun j => frameHessian (s j).frame) atTop (𝓝 H) ∧
      ∀ j, ‖matrixAction (frameHessian (s j).frame - H)‖ ≤
        (4 * Q * d₀.epsilon) * β ^ j / (1 - β) := by
  let M : ℕ → Matrix (Fin n) (Fin n) ℝ := fun j => frameHessian (s j).frame
  have hop (j : ℕ) : ‖matrixAction (M (j + 1) - M j)‖ ≤ (4 * Q * d₀.epsilon) * β ^ j := by
    let link := Classical.choice (hlinks j)
    have hh := norm_frameHessian_increment_le link.posDef (hinv j) link.hessian_increment
    rw [← link.frame_eq] at hh
    change ‖matrixAction (M (j + 1) - M j)‖ ≤ _ at hh
    rw [(s j).epsilon_eq] at hh
    convert hh using 1
    ring
  have hdist (j : ℕ) : dist (M j) (M (j + 1)) ≤ (4 * Q * d₀.epsilon) * β ^ j := by
    rw [dist_eq_norm, norm_sub_rev]
    exact (elementwise_matrix_norm_le_matrixAction_norm _).trans (hop j)
  obtain ⟨H, hlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric β (4 * Q * d₀.epsilon) hβone hdist)
  have hpsd : H.PosSemidef := posSemidef_of_matrix_tendsto (fun j => frameHessian_posSemidef _) hlim
  have hdet : H.det = 1 := by
    have hdlim : Tendsto (fun j => (M j).det) atTop (𝓝 H.det) :=
      continuous_id.matrix_det.continuousAt.tendsto.comp hlim
    have he : (fun j => (M j).det) = fun _ => (1 : ℝ) :=
      funext (fun j => frameHessian_det_of_abs_det_one (s j).determinant)
    rw [he] at hdlim
    exact tendsto_nhds_unique hdlim tendsto_const_nhds
  refine ⟨H, hpsd.posDef_iff_det_ne_zero.mpr (by rw [hdet]; norm_num), hdet, hlim, ?_⟩
  have hdop (j : ℕ) : dist (matrixAction (M j)) (matrixAction (M (j + 1))) ≤
      (4 * Q * d₀.epsilon) * β ^ j := by
    rw [dist_eq_norm, norm_sub_rev, ← matrixAction_sub_eq]
    exact hop j
  have hmap := continuous_matrixAction.continuousAt.tendsto.comp hlim
  intro j
  have ht := dist_le_of_le_geometric_of_tendsto β (4 * Q * d₀.epsilon) hβone hdop hmap j
  rwa [dist_eq_norm, ← matrixAction_sub_eq] at ht

end KLS
end
