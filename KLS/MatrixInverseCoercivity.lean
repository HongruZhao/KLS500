import KLS.MatrixTracePositive
import KLS.PositiveMatrixSquareRoot

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- An actual upper Loewner bound gives the reciprocal lower bound for the
actual inverse, with no simultaneous diagonalization assumption. -/
theorem inverse_lower_of_posDef_upper {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {K : ℝ} (hK : 0 < K) (hupper : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef) :
    (H⁻¹ - K⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  obtain ⟨R, hR, hRR⟩ := exists_symmetric_matrix_square_root hH.inv.posSemidef
  have hRR' : R * R = H⁻¹ := by simpa only [hR.eq] using hRR
  have hRu : IsUnit R.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hRR'
    rw [Matrix.det_mul, hz, zero_mul] at hh
    exact hH.inv.det_pos.ne' hh.symm
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have hmid : R * H * R = 1 := by
    calc
      R * H * R = R * H * (R * R) * R⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv R hRu, Matrix.mul_one]
      _ = R * (H * H⁻¹) * R⁻¹ := by rw [hRR']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv H hHu, Matrix.mul_one, Matrix.mul_nonsing_inv R hRu]
  have hgap := hupper.conjTranspose_mul_mul_same R
  have hRs : Rᴴ = R := (Matrix.isHermitian_iff_isSymm.mpr hR).eq
  simp only [hRs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hRR', hmid] at hgap
  have hs := hgap.smul (inv_nonneg.mpr hK.le)
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hK.ne', one_smul] using hs

/-- The inverse-metric matrix square controls the full ordered-entry
Frobenius square whenever the inverse has an actual scalar lower bound. -/
theorem trace_metric_square_lower {J X : Matrix (Fin n) (Fin n) ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hlow : (J - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hX : X.IsSymm) :
    c ^ 2 * matrixFrobeniusSq X ≤ (J * X * J * X).trace := by
  let P := J - c • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hP : P.PosSemidef := hlow
  have he : J = P + c • (1 : Matrix (Fin n) (Fin n) ℝ) := by dsimp [P]; abel
  have hX2 : (X * X).PosSemidef := by
    simpa only [(Matrix.isHermitian_iff_isSymm.mpr hX).eq] using Matrix.posSemidef_conjTranspose_mul_self X
  have hXPX : (X * P * X).PosSemidef := by
    simpa only [(Matrix.isHermitian_iff_isSymm.mpr hX).eq] using hP.conjTranspose_mul_mul_same X
  have hcross := trace_mul_nonneg_of_posSemidef hP hX2
  have hquad := trace_mul_nonneg_of_posSemidef hP hXPX
  have hid : (J * X * J * X).trace = c ^ 2 * (X * X).trace +
      2 * c * (P * (X * X)).trace + (P * (X * P * X)).trace := by
    rw [he]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    rw [Matrix.trace_mul_cycle X P X, Matrix.trace_mul_cycle X X P]
    simp only [Matrix.mul_assoc]
    ring
  rw [matrixFrobeniusSq_eq_trace_sq hX, hid]
  nlinarith

/-- The second variation of log det is quantitatively negative whenever
its actual positive matrix is bounded above by K times identity. -/
theorem inverse_trace_square_lower_of_upper {H X : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {K : ℝ} (hK : 0 < K)
    (hupper : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef)
    (hX : X.IsSymm) :
    (K⁻¹) ^ 2 * matrixFrobeniusSq X ≤ (H⁻¹ * X * H⁻¹ * X).trace :=
  trace_metric_square_lower (inv_nonneg.mpr hK.le) (inverse_lower_of_posDef_upper hH hK hupper) hX

end KLS
end
