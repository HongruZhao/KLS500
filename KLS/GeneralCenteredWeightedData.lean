import KLS.CenteredDensityCalibration

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A general central quadratic, including its non-unit determinant,
constructs a genuine normalized weighted datum. Both Jacobian constants
are retained in the transformed source and target potentials. -/
theorem exists_centered_whitened_weighted_data
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (c p : Space n) (a : ℝ) {r ρ ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hmap : r * ‖matrixAction (inverseSqrtMatrix A)‖ ≤ ρ)
    (hflat : ∀ x ∈ closedBall c ρ,
      |u x - centeredQuadratic A c p a x| ≤ ε * r ^ 2)
    (hdensity : ∀ y ∈ closedBall (0 : Space n) 1,
      |Real.exp (-W (c + r • matrixAction (inverseSqrtMatrix A) y) +
        V (gradient u (c + r • matrixAction (inverseSqrtMatrix A) y))) / A.det - 1| ≤ ε ^ 2) :
    ∃ d : NormalizedWeightedMomentData n 1 1,
      d.epsilon = ε ∧ d.c = 0 ∧
      d.u = quadraticallyRescaledPotential u c p a r ∘ matrixAction (inverseSqrtMatrix A) ∧
      ∀ y, weightedDataDensity d y =
        Real.exp (-W (c + r • matrixAction (inverseSqrtMatrix A) y) +
          V (gradient u (c + r • matrixAction (inverseSqrtMatrix A) y))) / A.det := by
  let B := inverseSqrtMatrix A
  have hBne : B.det ≠ 0 := inverseSqrtMatrix_det_ne_zero_of_posDef hA
  let e := affineMatrixEquiv B 0 hBne
  let u₁ := quadraticallyRescaledPotential u c p a r
  let W₁ := scalarNormalizedPotential W c r
  let V₁ := scalarNormalizedPotential V p r
  let K₁ := (scalarNormalizationEquiv p r hr.ne') '' K
  have hu₁ : ContDiff ℝ 1 u₁ := contDiff_quadraticallyRescaledPotential hu c p a r
  have hc₁ : StrictConvexOn ℝ univ u₁ := strictConvexOn_quadraticallyRescaledPotential hc c p a hr.ne'
  have hW₁ : Continuous W₁ := continuous_scalarNormalizedPotential hW c r
  have hV₁ : Continuous V₁ := continuous_scalarNormalizedPotential hV p r
  have hK₁ : IsClosed K₁ := isClosed_scalarNormalization_image hK p hr.ne'
  have hK₁c : Convex ℝ K₁ := convex_scalarNormalization_image hKc p hr.ne'
  have hpush₁ : (potentialMeasure W₁).map (gradient u₁) = (potentialMeasure V₁).restrict K₁ :=
    weighted_quadratic_rescaling_transport (hu.differentiable (by norm_num)) hW.measurable hV.measurable
      hpush c p a hr.ne'
  obtain ⟨D, hD⟩ := exists_lipschitzWith_quadraticallyRescaledPotential hLip c p a r
  let v := u₁ ∘ matrixAction B
  let W₂ := fun y => W₁ (matrixAction B y) - Real.log |B.det|
  let V₂ := fun q => V₁ (e.symm q) + Real.log |B.det|
  have hid (y : Space n) : Real.exp (-W₂ y + V₂ (gradient v y)) =
      Real.exp (-W (c + r • matrixAction B y) + V (gradient u (c + r • matrixAction B y))) / A.det := by
    rw [weighted_density_inverseSqrtMatrix_general (hu₁.differentiable (by norm_num)) hA,
      weighted_quadratic_rescaling_density_identity (hu.differentiable (by norm_num)) c p a hr.ne']
  have hmem {y : Space n} (hy : y ∈ closedBall (0 : Space n) 1) :
      c + r • matrixAction B y ∈ closedBall c ρ := by
    have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    calc
      _ ≤ r * (‖matrixAction B‖ * ‖y‖) := mul_le_mul_of_nonneg_left ((matrixAction B).le_opNorm y) hr.le
      _ ≤ r * ‖matrixAction B‖ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) hyn) hr.le
      _ ≤ ρ := hmap
  have hbound (y : Space n) (hy : y ∈ closedBall (0 : Space n) 1) :
      |normalizedQuadraticError v 0 0 0 ε y| ≤ 1 := by
    have he : v y - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y =
        (u (c + r • matrixAction B y) - centeredQuadratic A c p a (c + r • matrixAction B y)) / r ^ 2 := by
      rw [← centeredQuadratic_inverseSqrtMatrix hA]
      exact quadratic_rescaling_error_identity u A c p a hr.ne' (matrixAction B y)
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
    continuous_source := (hW₁.comp (matrixAction B).continuous).sub continuous_const
    continuous_target := (hV₁.comp e.symm.continuous).add continuous_const
    closed_target := e.toHomeomorph.isClosedMap _ hK₁
    convex_target := Convex.affine_image e.toAffineEquiv.toAffineMap hK₁c
    pushforward := weighted_moment_transport_inverseSqrtMatrix_general (hu₁.differentiable (by norm_num))
      hW₁.measurable hV₁.measurable hpush₁ hA
    epsilon_pos := hε
    density := fun y hy => by rw [hid y]; exact hdensity y hy
    bound := hbound }
  exact ⟨d, rfl, rfl, rfl, hid⟩

end KLS
end
