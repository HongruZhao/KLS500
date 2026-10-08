import KLS.VolumePreservingPotentialTransport

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma affineMatrixEquiv_zero_apply (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (x : Space n) : affineMatrixEquiv B 0 hB x = matrixAction B x := by
  change matrixAction B x + 0 = _
  simp

lemma matrix_equiv_volumePreserving (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : |B.det| = 1) :
    MeasurePreserving (affineMatrixEquiv B 0 (by intro hh; simp [hh] at hB)) volume volume := by
  refine ⟨(affineMatrixEquiv _ _ _).continuous.measurable, ?_⟩
  rw [map_volume_affineMatrixEquiv, abs_inv, hB, inv_one, ENNReal.ofReal_one, one_smul]

lemma gradient_comp_matrixAction {u : Space n → ℝ} (hu : Differentiable ℝ u)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    gradient (u ∘ matrixAction B) x = matrixAction B.transpose (gradient u (matrixAction B x)) := by
  have hd := (hu (matrixAction B x)).hasFDerivAt.comp x (matrixAction B).hasFDerivAt
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, hd.fderiv, inner_matrixAction_transpose, Matrix.transpose_transpose,
    inner_gradient_left]
  rfl

lemma gradient_symmetric_linear_conjugacy {u : Space n → ℝ} (hu : Differentiable ℝ u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hne : B.det ≠ 0) :
    gradient (u ∘ matrixAction B) ∘ (affineMatrixEquiv B 0 hne).symm =
      (affineMatrixEquiv B 0 hne) ∘ gradient u := by
  funext x
  dsimp only [Function.comp_apply]
  rw [gradient_comp_matrixAction hu, hB.eq, affineMatrixEquiv_zero_apply]
  congr 1
  have he := (affineMatrixEquiv B 0 hne).apply_symm_apply x
  rw [affineMatrixEquiv_zero_apply] at he
  exact congrArg (gradient u) he

/-- A symmetric determinant-modulus-one linear change preserves the actual
weighted moment transport class, with opposite source/target coordinate maps. -/
theorem weighted_moment_transport_symmetric_matrix
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hdet : |B.det| = 1) :
    let e := affineMatrixEquiv B 0 (by intro hh; simp [hh] at hdet)
    (potentialMeasure (W ∘ matrixAction B)).map (gradient (u ∘ matrixAction B)) =
      (potentialMeasure (V ∘ e.symm)).restrict (e '' K) := by
  dsimp only
  let e := affineMatrixEquiv B 0 (by intro hh; simp [hh] at hdet)
  have hh := weighted_gradient_transport_of_volumePreserving_conjugacy
    e.toHomeomorph.toMeasurableEquiv (matrix_equiv_volumePreserving B hdet) hW hV hpush
    (gradient_symmetric_linear_conjugacy hu hB (by intro hh; simp [hh] at hdet))
  have hsource : W ∘ e.toHomeomorph.toMeasurableEquiv = W ∘ matrixAction B := by
    funext x
    change W (e x) = W (matrixAction B x)
    exact congrArg W (affineMatrixEquiv_zero_apply B (by intro hz; simp [hz] at hdet) x)
  rw [hsource] at hh
  exact hh

end KLS
end
