import KLS.WeightedScalarRescaling
import KLS.QuantitativeWhiteningNorm
import KLS.WeightedWhiteningRegularity
import KLS.WeightedControlledOneStepImprovement

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual affine subtraction, quadratic rescaling, and determinant-one
whitening construct another member of the weighted data class. The smaller
density error is required on the smaller physical ball and is not inferred
from the preceding, weaker density bound. -/
theorem exists_rescaled_whitened_weighted_data
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hdet : A.det = 1)
    (p : Space n) (a : ℝ) {r ρ ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hmap : r * ‖matrixAction (inverseSqrtMatrix A)‖ ≤ ρ)
    (hflat : ∀ x ∈ closedBall (0 : Space n) ρ,
      |u x - centeredQuadratic A 0 p a x| ≤ ε * r ^ 2)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) ρ,
      |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2) :
    ∃ d : NormalizedWeightedMomentData n 1 1,
      d.epsilon = ε ∧ d.c = 0 ∧
      d.u = quadraticallyRescaledPotential u 0 p a r ∘ matrixAction (inverseSqrtMatrix A) ∧
      ∀ y, Real.exp (-d.W y + d.V (gradient d.u y)) =
        Real.exp (-W (r • matrixAction (inverseSqrtMatrix A) y) +
          V (gradient u (r • matrixAction (inverseSqrtMatrix A) y))) := by
  let B := inverseSqrtMatrix A
  have hB : B.IsSymm := inverseSqrtMatrix_isSymm A
  have hBdet : |B.det| = 1 := abs_det_inverseSqrtMatrix_of_det_one hA hdet
  have hBne : B.det ≠ 0 := inverseSqrtMatrix_det_ne_zero_of_posDef hA
  let e := affineMatrixEquiv B 0 hBne
  let u₁ := quadraticallyRescaledPotential u 0 p a r
  let W₁ := scalarNormalizedPotential W 0 r
  let V₁ := scalarNormalizedPotential V p r
  let K₁ := (scalarNormalizationEquiv p r hr.ne') '' K
  have hu₁ : ContDiff ℝ 1 u₁ := contDiff_quadraticallyRescaledPotential hu 0 p a r
  have hc₁ : StrictConvexOn ℝ univ u₁ := strictConvexOn_quadraticallyRescaledPotential hc 0 p a hr.ne'
  have hW₁ : Continuous W₁ := continuous_scalarNormalizedPotential hW 0 r
  have hV₁ : Continuous V₁ := continuous_scalarNormalizedPotential hV p r
  have hK₁ : IsClosed K₁ := isClosed_scalarNormalization_image hK p hr.ne'
  have hK₁c : Convex ℝ K₁ := convex_scalarNormalization_image hKc p hr.ne'
  have hpush₁ : (potentialMeasure W₁).map (gradient u₁) = (potentialMeasure V₁).restrict K₁ :=
    weighted_quadratic_rescaling_transport (hu.differentiable (by norm_num)) hW.measurable hV.measurable
      hpush 0 p a hr.ne'
  obtain ⟨D, hD⟩ := exists_lipschitzWith_quadraticallyRescaledPotential hLip 0 p a r
  let v := u₁ ∘ matrixAction B
  let W₂ := W₁ ∘ matrixAction B
  let V₂ := V₁ ∘ e.symm
  have hid (y : Space n) : Real.exp (-W₂ y + V₂ (gradient v y)) =
      Real.exp (-W (r • matrixAction B y) + V (gradient u (r • matrixAction B y))) := by
    rw [weighted_density_symmetric_matrix (hu₁.differentiable (by norm_num)) hB hBne,
      weighted_quadratic_rescaling_density_identity (hu.differentiable (by norm_num)) 0 p a hr.ne']
    simp only [zero_add]
  have hmem {y : Space n} (hy : y ∈ closedBall (0 : Space n) 1) :
      r • matrixAction B y ∈ closedBall (0 : Space n) ρ := by
    have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      _ ≤ r * (‖matrixAction B‖ * ‖y‖) := mul_le_mul_of_nonneg_left ((matrixAction B).le_opNorm y) hr.le
      _ ≤ r * ‖matrixAction B‖ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) hyn) hr.le
      _ ≤ ρ := hmap
  have hbound (y : Space n) (hy : y ∈ closedBall (0 : Space n) 1) :
      |normalizedQuadraticError v 0 0 0 ε y| ≤ 1 := by
    have he : v y - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y =
        (u (r • matrixAction B y) - centeredQuadratic A 0 p a (r • matrixAction B y)) / r ^ 2 := by
      rw [← centeredQuadratic_inverseSqrtMatrix hA]
      exact (quadratic_rescaling_error_identity u A 0 p a hr.ne' (matrixAction B y)).trans (by simp only [zero_add])
    have habs : |v y - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y| ≤ ε := by
      rw [he, abs_div, abs_of_pos (sq_pos_of_pos hr)]
      exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr (hflat _ (hmem hy))
    unfold normalizedQuadraticError
    rw [abs_div, abs_of_pos hε]
    exact (div_le_iff₀ hε).mpr (by simpa only [one_mul] using habs)
  let d : NormalizedWeightedMomentData n 1 1 := {
    u := v, W := W₂, V := V₂, L := D * ‖matrixAction B‖₊, K := e '' K₁, c := 0, epsilon := ε
    lipschitz := hD.comp (matrixAction B).lipschitzWith
    contDiff := hu₁.comp (matrixAction B).contDiff
    strictConvex := strictConvexOn_comp_matrixAction hc₁ hBne
    continuous_source := hW₁.comp (matrixAction B).continuous
    continuous_target := hV₁.comp e.symm.continuous
    closed_target := e.toHomeomorph.isClosedMap _ hK₁
    convex_target := Convex.affine_image e.toAffineEquiv.toAffineMap hK₁c
    pushforward := weighted_moment_transport_symmetric_matrix (hu₁.differentiable (by norm_num))
      hW₁.measurable hV₁.measurable hpush₁ hB hBdet
    epsilon_pos := hε
    density := fun y hy => by rw [hid y]; exact hdensity _ (hmem hy)
    bound := hbound }
  exact ⟨d, rfl, rfl, rfl, hid⟩

end KLS
end
