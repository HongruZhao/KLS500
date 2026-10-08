import KLS.TensorCommutatorComparison
import KLS.MatrixTracePositive
import KLS.HessianTraceEvolution

/-!
# An inverse-metric tensor comparison by a weighted commutator

The fully contracted tensor quadratic form is a genuine Kronecker quadratic
form. A two-slot commutator and symmetry yield the comparison directly,
without leaving coordinate-change invariance as an unproved premise.
-/

open Matrix
open scoped BigOperators Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

def tensorMetricForm (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    A i a * B j b * C k c * T i j k * T a b c

def tensorFlatVector (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (Fin n × Fin n) × Fin n → ℝ := fun p => T p.1.1 p.1.2 p.2

lemma tensorMetricForm_eq_kronecker (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    tensorMetricForm A B C T =
      tensorFlatVector T ⬝ᵥ (((A ⊗ₖ B) ⊗ₖ C) *ᵥ tensorFlatVector T) := by
  simp only [tensorMetricForm, tensorFlatVector, dotProduct, Matrix.mulVec,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma tensorMetricForm_swap_first (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i j k, T i j k = T j i k) :
    tensorMetricForm A B C T = tensorMetricForm B A C T := by
  unfold tensorMetricForm
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    arg 2; ext i
    arg 2; ext k
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hT j i k, hT b a c]
  ring

lemma tensorMetricForm_swap_last (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i j k, T i j k = T i k j) :
    tensorMetricForm A B C T = tensorMetricForm A C B T := by
  unfold tensorMetricForm
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
    arg 2; ext k
    arg 2; ext j
    arg 2; ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hT i k j, hT a c b]
  ring

lemma tensorMetricForm_eq_traceGram (A P : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hT : ∀ i, (T i).IsSymm) :
    tensorMetricForm A P P T = ∑ i, ∑ j, A i j * matrixTraceGram P T i j := by
  simp only [tensorMetricForm, matrixTraceGram,
    trace_inverse_hessian_contraction P _ _ hP (hT _), Finset.mul_sum]
  conv_lhs =>
    arg 2; ext i
    arg 2; ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring


/-- The two-slot commutator has a PSD coefficient matrix in the genuine
inverse metric. This is a matrix congruence identity, with no chosen basis. -/
lemma inverse_metric_two_slot_posSemidef {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.IsSymm) :
    (((B * H * B) ⊗ₖ H⁻¹ - B ⊗ₖ B) -
      (B ⊗ₖ B - H⁻¹ ⊗ₖ (B * H * B))).PosSemidef := by
  let J := H⁻¹
  let K := H * B
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit
  have hJK : J * K = B := by
    dsimp [J, K]
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  have hKJ : Kᴴ * J = B := by
    dsimp [J, K]
    have hBH : Bᴴ = B := (Matrix.isHermitian_iff_isSymm.mpr hB).eq
    rw [Matrix.conjTranspose_mul, hBH, hH.isHermitian.eq,
      mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
  have hBK : B * K = B * H * B := by simp only [K, mul_assoc]
  let L := K ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ) -
    (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ K
  have heq : Lᴴ * (J ⊗ₖ J) * L =
      (((B * H * B) ⊗ₖ J - B ⊗ₖ B) -
        (B ⊗ₖ B - J ⊗ₖ (B * H * B))) := by
    simp only [L, Matrix.conjTranspose_sub, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      ← Matrix.mul_kronecker_mul, one_mul, mul_one, hKJ, hJK, hBK]
  have hp := (hH.posSemidef.inv.kronecker hH.posSemidef.inv).conjTranspose_mul_mul_same L
  rwa [heq] at hp

lemma kronecker_sub_left_real {α β : Type*}
    (A B : Matrix α α ℝ) (C : Matrix β β ℝ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext p q
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

/-- The fully contracted inverse-metric comparison is a nonnegative
Kronecker quadratic form, using symmetry of the actual tensor. -/
theorem inverse_metric_tensorForm_comparison {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k) :
    tensorMetricForm B B H⁻¹ T ≤ tensorMetricForm (B * H * B) H⁻¹ H⁻¹ T := by
  have hE := inverse_metric_two_slot_posSemidef hH hB
  have hp := (hE.kronecker hH.posSemidef.inv).dotProduct_mulVec_nonneg (tensorFlatVector T)
  simp only [star_trivial, kronecker_sub_left_real, Matrix.sub_mulVec, dotProduct_sub] at hp
  simp only [← tensorMetricForm_eq_kronecker] at hp
  rw [tensorMetricForm_swap_first H⁻¹ (B * H * B) H⁻¹ T hfirst] at hp
  linarith

/-- The actual first and third contractions from the Hessian evolution,
with the genuine inverse Hessian and no unproved normalization step. -/
theorem inverse_metric_trace_tensor_comparison {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j) :
    (∑ i, ∑ j, H⁻¹ i j * (B * T i * B * T j).trace) ≤
      ∑ i, ∑ j, (B * H * B) i j * (H⁻¹ * T i * H⁻¹ * T j).trace := by
  have hT (i : Fin n) : (T i).IsSymm :=
    Matrix.IsSymm.ext (fun j k => (hlast i j k).symm)
  have he := inverse_metric_tensorForm_comparison hH hB T hfirst
  rw [tensorMetricForm_swap_last B B H⁻¹ T hlast,
    tensorMetricForm_swap_first B H⁻¹ B T hfirst,
    tensorMetricForm_eq_traceGram H⁻¹ B T hB hT,
    tensorMetricForm_eq_traceGram (B * H * B) H⁻¹ T hH.isHermitian.isSymm.inv hT] at he
  exact he


/-- The pointwise comparison for the actual third derivatives of a C³
potential. All tensor symmetries follow from the actual derivative theorem. -/
theorem hessianTraceGradientTerm_le_third {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (x : Space n) :
    hessianTraceGradientTerm φ B x ≤ hessianTraceThirdTerm φ B x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hT (i : Fin n) := hessianDerivative_symmetric hφ2 x i
  have hQ := matrixTraceGram_posSemidef (hpos x).posSemidef.inv
    (hessianDerivative φ x) hT
  unfold hessianTraceGradientTerm hessianTraceThirdTerm
  rw [← matrix_entrywise_contraction_eq_trace _ _ hQ.isHermitian.isSymm]
  exact inverse_metric_trace_tensor_comparison (hpos x) hB (hessianDerivative φ x)
    (fun i j k => coordinateDerivative_hessian_swap hφ i j k x)
    (fun i j k => (hT i |>.apply j k).symm)

end KLS
end

#print axioms KLS.tensorMetricForm_eq_kronecker
#print axioms KLS.tensorMetricForm_swap_first
#print axioms KLS.tensorMetricForm_swap_last
#print axioms KLS.tensorMetricForm_eq_traceGram
#print axioms KLS.inverse_metric_two_slot_posSemidef
#print axioms KLS.inverse_metric_tensorForm_comparison
#print axioms KLS.inverse_metric_trace_tensor_comparison
#print axioms KLS.hessianTraceGradientTerm_le_third
