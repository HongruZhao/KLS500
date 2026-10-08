import KLS.ThirdCumulant
import KLS.LocalRademacher
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Actual gradient energy of symmetric matrix quadratic tests

For every isotropic measure, the symmetric quadratic form xᵀMx has gradient
2Mx and finite actual gradient energy 4 times its squared Frobenius norm.
No fourth-moment or variance bound is needed for this energy normalization.
-/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped BigOperators ContDiff ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def matrixAction (M : Matrix (Fin n) (Fin n) ℝ) : Space n →L[ℝ] Space n :=
  M.toEuclideanLin.toContinuousLinearMap

lemma matrixAction_apply (M : Matrix (Fin n) (Fin n) ℝ) (x : Space n) (i : Fin n) :
    matrixAction M x i = ∑ j : Fin n, M i j * x j := rfl

lemma matrixQuadratic_eq_inner (M : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    matrixQuadratic M x = inner ℝ x (matrixAction M x) := by
  simp only [matrixQuadratic, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixAction_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma contDiff_matrixQuadratic (M : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ⊤ (matrixQuadratic M) := by
  have heq : matrixQuadratic M = fun x => inner ℝ x (matrixAction M x) :=
    funext (matrixQuadratic_eq_inner M)
  rw [heq]
  exact contDiff_id.inner ℝ (matrixAction M).contDiff

/-- The actual gradient, with no a.e. replacement or gradient convention change. -/
lemma gradient_matrixQuadratic (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (x : Space n) : gradient (matrixQuadratic M) x = (2 : ℝ) • matrixAction M x := by
  have hsym : M.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hM)
  have heq : matrixQuadratic M = fun x => inner ℝ x (matrixAction M x) :=
    funext (matrixQuadratic_eq_inner M)
  apply (toDual ℝ (Space n)).injective
  rw [toDual_gradient]
  ext v
  change fderiv ℝ (matrixQuadratic M) x v = inner ℝ ((2 : ℝ) • matrixAction M x) v
  have hd : fderiv ℝ (fun y : Space n => inner ℝ y (matrixAction M y)) x v =
      inner ℝ x (matrixAction M v) + inner ℝ v (matrixAction M x) := by
    simpa only [id_eq, ContinuousLinearMap.fderiv, fderiv_id,
      ContinuousLinearMap.id_apply] using
      fderiv_inner_apply ℝ (f := id) (g := matrixAction M) (x := x)
        differentiableAt_id (matrixAction M).differentiableAt v
  rw [heq, hd]
  simp only [inner_smul_left, conj_trivial]
  have hs : inner ℝ (matrixAction M x) v = inner ℝ x (matrixAction M v) := hsym x v
  rw [← hs, real_inner_comm v (matrixAction M x)]
  ring

lemma matrixAction_coordinate_eq_inner (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) (i : Fin n) :
    matrixAction M x i = inner ℝ x (WithLp.toLp 2 (M i)) := by
  rw [matrixAction_apply, inner_eq_coordinate_sum]

lemma matrixAction_norm_sq (M : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    ‖matrixAction M x‖ ^ 2 = ∑ i : Fin n,
      (inner ℝ x (WithLp.toLp 2 (M i))) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [matrixAction_coordinate_eq_inner]

lemma IsIsotropic.integrable_matrixAction_norm_sq {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => ‖matrixAction M x‖ ^ 2) μ := by
  simp_rw [matrixAction_norm_sq]
  exact integrable_finsetSum Finset.univ fun i _ => (hμ.memLp_inner _).integrable_sq

lemma IsIsotropic.integral_matrixAction_norm_sq {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, ‖matrixAction M x‖ ^ 2 ∂μ) = matrixFrobeniusSq M := by
  simp_rw [matrixAction_norm_sq]
  rw [integral_finsetSum Finset.univ fun i _ => (hμ.memLp_inner _).integrable_sq]
  simp_rw [hμ.integral_inner_sq, EuclideanSpace.real_norm_sq_eq]
  rfl

lemma norm_gradient_matrixQuadratic_sq (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (x : Space n) :
    ‖gradient (matrixQuadratic M) x‖ ^ 2 = 4 * ‖matrixAction M x‖ ^ 2 := by
  rw [gradient_matrixQuadratic M hM, norm_smul]
  norm_num [mul_pow]

lemma IsIsotropic.integrable_gradient_matrixQuadratic_sq {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    Integrable (fun x => ‖gradient (matrixQuadratic M) x‖ ^ 2) μ := by
  simp_rw [norm_gradient_matrixQuadratic_sq M hM]
  exact (hμ.integrable_matrixAction_norm_sq M).const_mul 4

/-- The exact real Dirichlet integral appearing in Letwin's normalization. -/
theorem IsIsotropic.integral_gradient_matrixQuadratic_sq {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (∫ x, ‖gradient (matrixQuadratic M) x‖ ^ 2 ∂μ) = 4 * matrixFrobeniusSq M := by
  simp_rw [norm_gradient_matrixQuadratic_sq M hM]
  rw [integral_const_mul, hμ.integral_matrixAction_norm_sq]

/-- The actual extended energy is finite and has the same exact value. -/
theorem IsIsotropic.energy_matrixQuadratic {μ : Measure (Space n)}
    (hμ : IsIsotropic μ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    energy μ (matrixQuadratic M) = ENNReal.ofReal (4 * matrixFrobeniusSq M) := by
  unfold energy
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hμ.integrable_gradient_matrixQuadratic_sq M hM)
    (Eventually.of_forall fun _ => sq_nonneg _), hμ.integral_gradient_matrixQuadratic_sq M hM]

end KLS
end

#print axioms KLS.gradient_matrixQuadratic
#print axioms KLS.IsIsotropic.integral_gradient_matrixQuadratic_sq
#print axioms KLS.IsIsotropic.energy_matrixQuadratic
