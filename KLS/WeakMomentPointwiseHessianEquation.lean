import KLS.GradientDerivativePeano

open MeasureTheory Matrix Set Filter InnerProductSpace Asymptotics
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Weak moment transport identifies the genuine coordinate Hessian at every
 point where the actual gradient is differentiable. Quadratic upper and lower
 tests are constructed from the proved Peano expansion. -/
theorem weak_moment_hessian_equation_at_gradient_differentiableAt
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hg : DifferentiableAt ℝ (gradient u) x₀) :
    (coordinateHessian u x₀).PosDef ∧
      (coordinateHessian u x₀).det = Real.exp (-u x₀ + V (gradient u x₀)) ∧
      HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x₀)) x₀ := by
  have hu := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  let A := coordinateHessian u x₀
  have hpsd : A.PosSemidef := coordinateHessian_posSemidef_of_gradient_differentiableAt hu hc hg
  have hder := hasFDerivAt_gradient_of_differentiableAt_gradient hu hg
  have hpeano := quadratic_peano_of_hasFDerivAt_gradient hu hpsd.isHermitian.isSymm hder
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∀ᶠ y in 𝓝 x₀,
      |u y-centeredQuadratic A x₀ (gradient u x₀) (u x₀) y| ≤ ε*‖y-x₀‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hpeano.bound hε
  have hge : Real.exp (-u x₀+V (gradient u x₀)) ≤ A.det := by
    by_contra hnot
    have hgap := lt_of_not_ge hnot
    have hd : Continuous (fun ε : ℝ => (A+ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    have he : ∀ᶠ ε in 𝓝 (0 : ℝ), (A+ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det <
        Real.exp (-u x₀+V (gradient u x₀)) :=
      hd.continuousAt.eventually (Iio_mem_nhds (by simpa using hgap))
    obtain ⟨ε,hε,_,hdet⟩ := exists_pos_lt_of_eventually_zero zero_lt_one he
    have hplus := posDef_add_scalar_one_of_posSemidef hpsd hε
    have ht : ∀ᶠ y in 𝓝 x₀, u y ≤ centeredQuadratic
        (A+ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x₀ (gradient u x₀) (u x₀) y := by
      filter_upwards [hsmall (ε/2) (by positivity)] with y hy
      have hdiff := centeredQuadratic_add_scalar_one_difference A ε x₀ (gradient u x₀) (u x₀) y
      have hh := (abs_le.mp hy).2
      linarith
    have hi := moment_det_ge_density_of_positive_quadratic_upper_touch hLip hc hV hK hKc hpush
      hplus x₀ (gradient u x₀) ht
    exact (not_le_of_gt hdet) hi
  have hpos : A.PosDef := hpsd.posDef_iff_det_ne_zero.mpr ((Real.exp_pos _).trans_le hge).ne'
  have hle : A.det ≤ Real.exp (-u x₀+V (gradient u x₀)) := by
    by_contra hnot
    have hgap := lt_of_not_ge hnot
    obtain ⟨δ,hδ,hposminus⟩ := exists_pos_sub_scalar_one_posDef hpos
    have hd : Continuous (fun ε : ℝ => (A-ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
      (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
    have he : ∀ᶠ ε in 𝓝 (0 : ℝ), Real.exp (-u x₀+V (gradient u x₀)) <
        (A-ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
      hd.continuousAt.eventually (Ioi_mem_nhds (by simpa using hgap))
    obtain ⟨ε,hε,hεδ,hdet⟩ := exists_pos_lt_of_eventually_zero hδ he
    have hminus : (A-ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
      hposminus ε (by simpa only [abs_of_pos hε] using hεδ)
    have ht : ∀ᶠ y in 𝓝 x₀, centeredQuadratic
        (A-ε • (1 : Matrix (Fin n) (Fin n) ℝ)) x₀ (gradient u x₀) (u x₀) y ≤ u y := by
      filter_upwards [hsmall (ε/2) (by positivity)] with y hy
      have hdiff := centeredQuadratic_sub_scalar_one_difference A ε x₀ (gradient u x₀) (u x₀) y
      have hh := (abs_le.mp hy).1
      linarith
    have hi := moment_det_le_density_of_positive_quadratic_lower_touch hLip hc hV hK hKc hpush
      hminus x₀ (gradient u x₀) ht
    exact (not_le_of_gt hdet) hi
  exact ⟨hpos,le_antisymm hle hge,hder⟩

end KLS
end
