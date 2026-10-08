import KLS.QuadraticAlexandrovViscosity

/-! Quantitative positivity of the quadratic form of a positive matrix, and
small scalar-identity perturbations. The lower bound comes from compactness
of the actual Euclidean unit sphere. -/

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

lemma matrixAction_add_matrices (A B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    matrixAction (A + B) x = matrixAction A x + matrixAction B x := by
  ext i
  simp only [matrixAction_apply, Matrix.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

lemma matrixAction_sub_matrices (A B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    matrixAction (A - B) x = matrixAction A x - matrixAction B x := by
  ext i
  simp only [matrixAction_apply, Matrix.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma matrixAction_one_apply (x : Space n) :
    matrixAction (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  ext i
  simp [matrixAction_apply, Matrix.one_apply]

lemma exists_pos_inner_matrixAction_lower_bound {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ κ > 0, ∀ x : Space n, κ * ‖x‖ ^ 2 ≤ inner ℝ x (matrixAction A x) := by
  have hc : Continuous (fun x : Space n => inner ℝ x (matrixAction A x)) :=
    continuous_id.inner (matrixAction A).continuous
  obtain ⟨κ, hκ, hgap⟩ := exists_pos_uniform_gap_on_compact
    (isCompact_sphere (0 : Space n) 1) hc continuous_const (fun x hx => by
      apply inner_matrixAction_pos hA
      intro heq
      subst x
      simp at hx)
  refine ⟨κ, hκ, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : Space n := ‖x‖⁻¹ • x
  have hz : z ∈ sphere (0 : Space n) 1 := by
    simp only [mem_sphere, dist_zero_right, z, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  have hlower : κ ≤ inner ℝ z (matrixAction A z) := by linarith [hgap z hz]
  have hxid : ‖x‖ • z = x := by simp [z, smul_smul, hnorm.ne']
  have hquad : inner ℝ x (matrixAction A x) = ‖x‖ ^ 2 * inner ℝ z (matrixAction A z) := by
    conv_lhs => rw [← hxid]
    simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
    ring
  rw [hquad]
  nlinarith [mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖x‖)]

lemma exists_pos_sub_scalar_one_posDef {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  obtain ⟨δ, hδ, hlower⟩ := exists_pos_inner_matrixAction_lower_bound hA
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact hA.isHermitian.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all ε))
  intro w hw
  let x : Space n := WithLp.toLp 2 w
  have hx : x ≠ 0 := by
    intro hx
    apply hw
    ext i
    exact congrArg (fun v : Space n => v i) hx
  have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hεlt : ε < δ := (le_abs_self ε).trans_lt hε
  have hpos : 0 < inner ℝ x (matrixAction (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x) := by
    rw [matrixAction_sub_matrices, matrixAction_smul_scalar, matrixAction_one_apply,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [hlower x, mul_pos (sub_pos.mpr hεlt) hnorm]
  simpa only [x, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using hpos

lemma centeredQuadratic_add_scalar_one_difference (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    centeredQuadratic (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x₀ p c x -
      centeredQuadratic A x₀ p c x = (ε / 2) * ‖x - x₀‖ ^ 2 := by
  simp only [centeredQuadratic, matrixAction_add_matrices, matrixAction_smul_scalar,
    matrixAction_one_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

lemma centeredQuadratic_sub_scalar_one_difference (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (x₀ p : Space n) (c : ℝ) (x : Space n) :
    centeredQuadratic (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x₀ p c x -
      centeredQuadratic A x₀ p c x = -(ε / 2) * ‖x - x₀‖ ^ 2 := by
  have heq : A - ε • (1 : Matrix (Fin n) (Fin n) ℝ) = A + (-ε) • 1 := by
    simp [sub_eq_add_neg]
  rw [heq, centeredQuadratic_add_scalar_one_difference]
  ring


end KLS
end

#print axioms KLS.exists_pos_inner_matrixAction_lower_bound
#print axioms KLS.exists_pos_sub_scalar_one_posDef
