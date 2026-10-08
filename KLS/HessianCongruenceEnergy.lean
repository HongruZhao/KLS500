import KLS.HessianMatrixMean
import KLS.SteinMatrixContraction

/-! # Actual entrywise gradients and energy of a fixed Hessian congruence -/

open Matrix InnerProductSpace MeasureTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma contDiff_matrix_mul_const {A : Space n → Matrix (Fin n) (Fin n) ℝ} {k : ℕ∞ω}
    (hA : ContDiff ℝ k A) (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ k (fun y => A y * B) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ k (fun y => ∑ l, A y i l * B l j)
  exact ContDiff.sum (fun l _ => (contDiff_matrix_entry hA i l).mul contDiff_const)

lemma coordinateDerivativeMatrix_mul_const {A : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContDiff ℝ 2 A) (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivativeMatrix (fun y => A y * B) i x = coordinateDerivativeMatrix A i x * B := by
  ext a b
  change coordinateDerivative (fun y => ∑ l, A y a l * B l b) i x =
    ∑ l, coordinateDerivative (fun y => A y a l) i x * B l b
  rw [coordinateDerivative_sum (f := fun l y => A y a l * B l b)
    (fun l => ((contDiff_matrix_entry hA a l).differentiable (by norm_num) x).mul
      (differentiableAt_const (c := B l b)))]
  apply Finset.sum_congr rfl
  intro l _
  rw [coordinateDerivative_mul ((contDiff_matrix_entry hA a l).differentiable (by norm_num) x)
    (differentiableAt_const (c := B l b))]
  simp [coordinateDerivative]

lemma matrix_congruence_isSymm (R : Matrix (Fin n) (Fin n) ℝ)
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) : (R * T * R.transpose).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have heq : (R * T * R.transpose).transpose = R * T * R.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hT.eq]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun M => M i j) heq

lemma matrix_congruence_entrywise_inner
    (R U V : Matrix (Fin n) (Fin n) ℝ) (hV : V.IsSymm) :
    (∑ i, ∑ j, (R * U * R.transpose) i j * (R * V * R.transpose) i j) =
      ((R.transpose * R) * U * (R.transpose * R) * V).trace := by
  rw [matrix_entrywise_contraction_eq_trace _ _ (matrix_congruence_isSymm R hV)]
  calc
    ((R * U * R.transpose) * (R * V * R.transpose)).trace =
        (R * (U * R.transpose * R * V) * R.transpose).trace := by
      simp only [Matrix.mul_assoc]
    _ = (R.transpose * R * (U * R.transpose * R * V)).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

def hessianCongruence (φ : Space n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ := R * coordinateHessian φ x * R.transpose

lemma contDiff_hessianCongruence {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (R : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ 2 (hessianCongruence φ R) :=
  contDiff_matrix_mul_const (contDiff_matrix_const_mul (contDiff_coordinateHessian_matrix hφ) R) R.transpose

lemma coordinateDerivative_hessianCongruence {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (R : Matrix (Fin n) (Fin n) ℝ) (x : Space n) (i a b : Fin n) :
    coordinateDerivative (fun y => hessianCongruence φ R y a b) i x =
      (R * hessianDerivative φ x i * R.transpose) a b := by
  have h := coordinateDerivativeMatrix_mul_const
    (contDiff_matrix_const_mul (contDiff_coordinateHessian_matrix hφ) R) R.transpose i x
  rw [coordinateDerivativeMatrix_const_mul (contDiff_coordinateHessian_matrix hφ)] at h
  exact congrArg (fun M => M a b) h

/-- The summed genuine scalar energies equal the required noncommuting
trace term, not the generally different Tr(B²T²) contraction. -/
theorem sum_inverseHessianGradientForm_hessianCongruence {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (R : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    (∑ a, ∑ b, inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b) x) =
      hessianTraceGradientTerm φ (R.transpose * R) x := by
  unfold inverseHessianGradientForm
  simp_rw [coordinateDerivative_hessianCongruence hφ]
  have hswap : (∑ a, ∑ b, ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      (R * hessianDerivative φ x i * R.transpose) a b *
      (R * hessianDerivative φ x j * R.transpose) a b) =
      ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        (∑ a, ∑ b, (R * hessianDerivative φ x i * R.transpose) a b *
          (R * hessianDerivative φ x j * R.transpose) a b) := by
    simp_rw [Finset.mul_sum, mul_assoc]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [matrix_congruence_entrywise_inner _ _ _
    (hessianDerivative_symmetric (hφ.of_le (by norm_num)) x _)]
  rfl

theorem memLp_hessianCongruence_entry {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    MemLp (fun x => hessianCongruence φ R x a b) 2 (potentialMeasure φ) := by
  change MemLp (fun x => (R * coordinateHessian φ x * R.transpose) a b) 2 (potentialMeasure φ)
  exact memLp_matrix_comp_of_bounded_range (φ := φ)
    (F := fun M => (R * M * R.transpose) a b)
    (contDiff_coordinateHessian_matrix hφ).continuous hH
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem a b) 2

/-- Each entry energy is integrable when the actual summed trace energy is.
The domination follows from nonnegativity of all the actual scalar energies. -/
theorem integrable_hessianCongruence_entry_energy {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (hessianTraceGradientTerm φ (R.transpose * R)) (potentialMeasure φ))
    (a b : Fin n) :
    Integrable (inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b)) (potentialMeasure φ) := by
  have hf : ContDiff ℝ 1 (fun y => hessianCongruence φ R y a b) :=
    (contDiff_matrix_entry (contDiff_hessianCongruence hφ R) a b).of_le (by norm_num)
  apply hA.mono' (continuous_inverseHessianGradientForm (hφ.of_le (by norm_num)) hf hpos).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (inverseHessianGradientForm_nonneg hpos _ _),
    ← sum_inverseHessianGradientForm_hessianCongruence hφ R x]
  have h1 : inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a b) x ≤
      ∑ j, inverseHessianGradientForm φ (fun y => hessianCongruence φ R y a j) x :=
    Finset.single_le_sum (fun j _ => inverseHessianGradientForm_nonneg hpos
      (fun y => hessianCongruence φ R y a j) x) (Finset.mem_univ b)
  exact h1.trans (Finset.single_le_sum (fun i _ => Finset.sum_nonneg
    (fun j _ => inverseHessianGradientForm_nonneg hpos
      (fun y => hessianCongruence φ R y i j) x)) (Finset.mem_univ a))

end KLS
end

#print axioms KLS.sum_inverseHessianGradientForm_hessianCongruence
#print axioms KLS.memLp_hessianCongruence_entry
#print axioms KLS.integrable_hessianCongruence_entry_energy
