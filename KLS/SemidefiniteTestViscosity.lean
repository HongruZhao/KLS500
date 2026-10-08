import KLS.SmoothAlexandrovViscosity

/-! The local C2 test inequalities include singular positive semidefinite
Hessians. Upper tests are regularized by epsilon I; a singular lower test has
zero determinant, so positivity of the density supplies its inequality. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma posDef_add_scalar_one_of_posSemidef {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact hA.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all ε))
  intro w hw
  let x : Space n := WithLp.toLp 2 w
  have hx : x ≠ 0 := by
    intro hx
    apply hw
    ext i
    exact congrArg (fun v : Space n => v i) hx
  have hpos : 0 < inner ℝ x (matrixAction (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x) := by
    rw [matrixAction_add_matrices, matrixAction_smul_scalar, matrixAction_one_apply,
      inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    exact add_pos_of_nonneg_of_pos (inner_matrixAction_nonneg hA x)
      (mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hx)))
  simpa only [x, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using hpos

theorem det_ge_density_of_c2_semidefinite_upper_touch
    {u f ψ : Space n → ℝ} (hu : Continuous u) {x₀ : Space n}
    (hf : ContinuousAt f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (coordinateHessian ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (coordinateHessian ψ x₀).det := by
  by_contra hnot
  let A := coordinateHessian ψ x₀
  have hgap : A.det < f x₀ := lt_of_not_ge hnot
  have hd : Continuous (fun ε : ℝ => (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det < f x₀ :=
    hd.continuousAt.eventually (Iio_mem_nhds (by simpa using hgap))
  obtain ⟨ε, hε, _, hdet⟩ := exists_pos_lt_of_eventually_zero zero_lt_one he
  have hAplus := posDef_add_scalar_one_of_posSemidef hH hε
  have htaylor := eventually_abs_sub_centeredQuadratic_le_sq hψ hH
    (div_pos hε (by norm_num : (0 : ℝ) < 2))
  have hquad : ∀ᶠ x in 𝓝 x₀,
      u x ≤ centeredQuadratic (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ))
        x₀ (gradient ψ x₀) (ψ x₀) x := by
    filter_upwards [htouch, htaylor] with x hx ht
    have hdifference := centeredQuadratic_add_scalar_one_difference A ε x₀ (gradient ψ x₀) (ψ x₀) x
    have hupper := (abs_le.mp ht).2
    change ψ x - centeredQuadratic A x₀ (gradient ψ x₀) (ψ x₀) x ≤ _ at hupper
    linarith
  have hineq := det_ge_density_of_positive_quadratic_upper_touch hu hf hMA hAplus hcontact hquad
  exact (not_le_of_gt hdet) hineq

theorem det_le_density_of_c2_semidefinite_lower_touch
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {x₀ : Space n} (hf : ContinuousAt f x₀) (hfpos : 0 ≤ f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (coordinateHessian ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (coordinateHessian ψ x₀).det ≤ f x₀ := by
  by_cases hdet : (coordinateHessian ψ x₀).det = 0
  · rwa [hdet]
  · exact det_le_density_of_c2_lower_touch hu huc hf hfpos hMA hψ
      (hH.posDef_iff_det_ne_zero.mpr hdet) hcontact htouch

end KLS
end

#print axioms KLS.det_ge_density_of_c2_semidefinite_upper_touch
#print axioms KLS.det_le_density_of_c2_semidefinite_lower_touch
