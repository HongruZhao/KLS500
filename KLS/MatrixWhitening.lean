import KLS.Definitions
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Actual inverse square roots for covariance whitening

The whitening matrix is the inverse of the continuous-functional-calculus
positive square root. Cancellation and convergence are proved for this actual
matrix, rather than assumed as properties of an abstract whitening operation.
-/

open Matrix Set Filter
open scoped Topology MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace KLS

/-- The actual inverse positive square root used in affine whitening. -/
def inverseSqrtMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (CFC.sqrt A)⁻¹

theorem inverseSqrtMatrix_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (inverseSqrtMatrix A).IsSymm :=
  (CFC.sqrt_nonneg A).posSemidef.inv.isHermitian.isSymm

/-- A genuine positive-definite covariance is transformed to the identity by
its actual inverse positive square root. -/
theorem inverseSqrtMatrix_mul_self_mul_transpose {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    inverseSqrtMatrix A * A * (inverseSqrtMatrix A).transpose = 1 := by
  have hunit : IsUnit (CFC.sqrt A) :=
    (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hdet : IsUnit (CFC.sqrt A).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  rw [(inverseSqrtMatrix_isSymm A).eq]
  unfold inverseSqrtMatrix
  calc
    (CFC.sqrt A)⁻¹ * A * (CFC.sqrt A)⁻¹ =
        (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by
      rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
    _ =
        ((CFC.sqrt A)⁻¹ * CFC.sqrt A) * (CFC.sqrt A * (CFC.sqrt A)⁻¹) := by
      simp only [mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, one_mul]

/-- Actual matrix inversion is continuous at the identity. -/
theorem continuousAt_matrix_inverse_one {n : ℕ} :
    ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) 1 := by
  apply continuousAt_matrix_inv
  simpa only [Matrix.det_one, show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using
    (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0))

/-- Positive-semidefinite matrices converging to the identity have inverse
square roots converging to the identity. Finite-dimensional CFC continuity and
actual inverse continuity supply both steps. -/
theorem tendsto_inverseSqrtMatrix_one {n : ℕ} {ι : Type*} {l : Filter ι}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Tendsto A l (𝓝 1)) (hpos : ∀ᶠ k in l, (A k).PosSemidef) :
    Tendsto (fun k => inverseSqrtMatrix (A k)) l (𝓝 1) := by
  have hwithin : Tendsto A l (𝓝[{B : Matrix (Fin n) (Fin n) ℝ | 0 ≤ B}] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hA, hpos.mono (fun k hk => hk.nonneg)⟩
  have hsqrt : Tendsto (fun k => CFC.sqrt (A k)) l (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    simpa only [CFC.sqrt_one, Function.comp_def] using
      (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ) 1
        (show (1 : Matrix (Fin n) (Fin n) ℝ) ∈ {a | 0 ≤ a} from (show (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 from zero_le_one))).tendsto.comp hwithin
  simpa only [inverseSqrtMatrix, Function.comp_def, inv_one] using
    continuousAt_matrix_inverse_one.tendsto.comp hsqrt

/-- Positive-semidefinite matrices tending to the identity are eventually
positive definite, because their determinants tend to one. -/
theorem eventually_posDef_of_tendsto_one {n : ℕ} {ι : Type*} {l : Filter ι}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Tendsto A l (𝓝 1)) (hpos : ∀ᶠ k in l, (A k).PosSemidef) :
    ∀ᶠ k in l, (A k).PosDef := by
  have hdet : Tendsto (fun k => (A k).det) l (𝓝 (1 : ℝ)) := by
    simpa only [Matrix.det_one, Function.comp_def, id_eq] using
      continuous_id.matrix_det.continuousAt.tendsto.comp hA
  have hne : ∀ᶠ k in l, (A k).det ≠ 0 := hdet.eventually_ne (by norm_num)
  filter_upwards [hpos, hne] with k hk hkn
  exact hk.posDef_iff_det_ne_zero.mpr hkn

end KLS
end

#print axioms KLS.inverseSqrtMatrix_mul_self_mul_transpose
#print axioms KLS.tendsto_inverseSqrtMatrix_one
#print axioms KLS.eventually_posDef_of_tendsto_one
