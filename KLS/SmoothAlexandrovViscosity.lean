import KLS.SecondOrderLocalTaylor
import KLS.PositiveMatrixPerturbation

/-! Genuine local C2 test-function viscosity inequalities, obtained from the
proved quadratic inequalities by actual Taylor bounds and determinant
continuity. No differentiability of the weak solution is assumed. -/

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma exists_pos_lt_of_eventually_zero {P : ℝ → Prop} {δ : ℝ} (hδ : 0 < δ)
    (hP : ∀ᶠ ε in 𝓝 (0 : ℝ), P ε) : ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hP
  let ε := min r δ / 2
  have hε : 0 < ε := div_pos (lt_min hr hδ) (by norm_num)
  have hεr : ε < r := by dsimp [ε]; have := min_le_left r δ; linarith
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_right r δ; linarith
  refine ⟨ε, hε, hεδ, hball ?_⟩
  simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε] using hεr

/-- A local C2 upper test with positive definite actual Hessian satisfies
`det D2(test) >= f` at the contact point. -/
theorem det_ge_density_of_c2_upper_touch
    {u f ψ : Space n → ℝ} (hu : Continuous u) {x₀ : Space n}
    (hf : ContinuousAt f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (coordinateHessian ψ x₀).PosDef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (coordinateHessian ψ x₀).det := by
  by_contra hnot
  let A := coordinateHessian ψ x₀
  have hgap : A.det < f x₀ := lt_of_not_ge hnot
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_sub_scalar_one_posDef hH
  have hd : Continuous (fun ε : ℝ => (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det < f x₀ :=
    hd.continuousAt.eventually (Iio_mem_nhds (by simpa using hgap))
  obtain ⟨ε, hε, hεδ, hdet⟩ := exists_pos_lt_of_eventually_zero hδ he
  have hAplus : (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    have hh := hpos (-ε) (by simpa only [abs_neg, abs_of_pos hε] using hεδ)
    simpa only [neg_smul, sub_neg_eq_add] using hh
  have htaylor := eventually_abs_sub_centeredQuadratic_le_sq hψ hH.posSemidef
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

/-- A local C2 lower test with positive definite actual Hessian satisfies
`det D2(test) <= f` at the contact point. -/
theorem det_le_density_of_c2_lower_touch
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {x₀ : Space n} (hf : ContinuousAt f x₀) (hfpos : 0 ≤ f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (coordinateHessian ψ x₀).PosDef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (coordinateHessian ψ x₀).det ≤ f x₀ := by
  by_contra hnot
  let A := coordinateHessian ψ x₀
  have hgap : f x₀ < A.det := lt_of_not_ge hnot
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_sub_scalar_one_posDef hH
  have hd : Continuous (fun ε : ℝ => (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), f x₀ < (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    hd.continuousAt.eventually (Ioi_mem_nhds (by simpa using hgap))
  obtain ⟨ε, hε, hεδ, hdet⟩ := exists_pos_lt_of_eventually_zero hδ he
  have hAminus : (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    hpos ε (by simpa only [abs_of_pos hε] using hεδ)
  have htaylor := eventually_abs_sub_centeredQuadratic_le_sq hψ hH.posSemidef
    (div_pos hε (by norm_num : (0 : ℝ) < 2))
  have hquad : ∀ᶠ x in 𝓝 x₀,
      centeredQuadratic (A - ε • (1 : Matrix (Fin n) (Fin n) ℝ))
        x₀ (gradient ψ x₀) (ψ x₀) x ≤ u x := by
    filter_upwards [htouch, htaylor] with x hx ht
    have hdifference := centeredQuadratic_sub_scalar_one_difference A ε x₀ (gradient ψ x₀) (ψ x₀) x
    have hlower := (abs_le.mp ht).1
    change -(ε / 2 * ‖x - x₀‖ ^ 2) ≤
      ψ x - centeredQuadratic A x₀ (gradient ψ x₀) (ψ x₀) x at hlower
    linarith
  have hineq := det_le_density_of_positive_quadratic_lower_touch hu huc hf hfpos hMA hAminus hcontact hquad
  exact (not_le_of_gt hdet) hineq

end KLS
end

#print axioms KLS.det_ge_density_of_c2_upper_touch
#print axioms KLS.det_le_density_of_c2_lower_touch
