import KLS.GeneralWeightedMatrixTransport
import KLS.MomentDensityHolder

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_relative_density_sub_one_le {f : Space n → ℝ} {c x : Space n}
    (hfc : 0 < f c) {A α : ℝ}
    (hbound : |f x - f c| ≤ A * ‖x - c‖ ^ α) :
    |f x / f c - 1| ≤ (A / f c) * ‖x - c‖ ^ α := by
  have he : f x / f c - 1 = (f x - f c) / f c := by field_simp
  rw [he, abs_div, abs_of_pos hfc]
  convert div_le_div_of_nonneg_right hbound hfc.le using 1
  ring

/-- The actual positive Alexandrov density has a relative Hölder modulus
around every source point. The exponent is derived from the proved section
iteration, and the central value is the genuine density exp(-u+V(gradient u)). -/
theorem exists_local_relative_moment_density_holder
    (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) (hVc : ConvexOn ℝ univ V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (c : Space n) :
    ∃ R α C : ℝ, 0 < R ∧ 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ x ∈ closedBall c R,
        |Real.exp (-u x + V (gradient u x)) /
          Real.exp (-u c + V (gradient u c)) - 1| ≤ C * ‖x - c‖ ^ α := by
  obtain ⟨R, α, A, hR, hα, hα1, hA, hbound⟩ :=
    exists_local_momentMongeAmpereDensity_holder_bound hn hLip hc hV hVc hK hKc hpush c
  refine ⟨R, α, A / Real.exp (-u c + V (gradient u c)), hR, hα, hα1,
    div_pos hA (Real.exp_pos _), ?_⟩
  intro x hx
  apply abs_relative_density_sub_one_le
    (f := fun y => Real.exp (-u y + V (gradient u y)))
    (c := c) (x := x) (A := A) (α := α) (Real.exp_pos _)
  simpa only [momentMongeAmpereDensity, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    hbound c (mem_closedBall_self hR.le) x hx

lemma inverseSqrtMatrix_det_ne_zero_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (inverseSqrtMatrix A).det ≠ 0 := by
  intro hz
  have hh := abs_det_inverseSqrtMatrix_sq hA
  rw [hz, abs_zero, zero_pow (by norm_num)] at hh
  exact (one_div_pos.mpr hA.det_pos).ne' hh.symm

lemma exists_posDef_matrix_with_det_of_pos (hn : 0 < n) {d : ℝ} (hd : 0 < d) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A.det = d := by
  refine ⟨(d ^ (n : ℝ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ),
    Matrix.PosDef.one.smul (Real.rpow_pos_of_pos hd _), ?_⟩
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
  exact Real.rpow_inv_natCast_pow hd.le hn.ne'

theorem weighted_moment_transport_inverseSqrtMatrix_general
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    let B := inverseSqrtMatrix A
    let e := affineMatrixEquiv B 0 (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
    (potentialMeasure (fun y => W (matrixAction B y) - Real.log |B.det|)).map
      (gradient (u ∘ matrixAction B)) =
      (potentialMeasure (fun q => V (e.symm q) + Real.log |B.det|)).restrict (e '' K) :=
  weighted_moment_transport_general_symmetric_matrix hu hW hV hpush
    (inverseSqrtMatrix_isSymm A) (inverseSqrtMatrix_det_ne_zero_of_posDef hA)

/-- The actual non-unit whitening divides the original density by det A.
Thus choosing det A equal to the central density is a genuine transport
normalization, with both Jacobian constants retained. -/
theorem weighted_density_inverseSqrtMatrix_general
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (y : Space n) :
    let B := inverseSqrtMatrix A
    let e := affineMatrixEquiv B 0 (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
    Real.exp (-(W (matrixAction B y) - Real.log |B.det|) +
      (V (e.symm (gradient (u ∘ matrixAction B) y)) + Real.log |B.det|)) =
      Real.exp (-W (matrixAction B y) + V (gradient u (matrixAction B y))) / A.det := by
  dsimp only
  rw [weighted_density_general_symmetric_matrix hu (inverseSqrtMatrix_isSymm A)
    (inverseSqrtMatrix_det_ne_zero_of_posDef hA), abs_det_inverseSqrtMatrix_sq hA]
  ring

end KLS
end
