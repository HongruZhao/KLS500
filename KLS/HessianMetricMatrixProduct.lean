import KLS.HessianMetricProduct

/-! # Entrywise diffusion and actual trace-product calculus -/

open Matrix InnerProductSpace
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

def coordinateDerivativeMatrix (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => coordinateDerivative (fun y => A y a b) i x

def hessianMetricDiffusionMatrix (φ V : Space n → ℝ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => hessianMetricDiffusion φ V (fun y => A y a b) x

lemma contDiff_matrix_entry {A : Space n → Matrix (Fin n) (Fin n) ℝ} {k : ℕ∞ω}
    (hA : ContDiff ℝ k A) (i j : Fin n) : ContDiff ℝ k (fun y => A y i j) :=
  contDiff_pi.mp (contDiff_pi.mp hA i) j

lemma contDiff_matrix_const_mul {A : Space n → Matrix (Fin n) (Fin n) ℝ} {k : ℕ∞ω}
    (hA : ContDiff ℝ k A) (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ k (fun y => B * A y) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ k (fun y => ∑ l, B i l * A y l j)
  exact ContDiff.sum (fun l _ => contDiff_const.mul (contDiff_matrix_entry hA l j))

lemma coordinateDerivativeMatrix_const_mul {A : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContDiff ℝ 2 A) (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivativeMatrix (fun y => B * A y) i x = B * coordinateDerivativeMatrix A i x := by
  ext a b
  change coordinateDerivative (fun y => ∑ l, B a l * A y l b) i x =
    ∑ l, B a l * coordinateDerivative (fun y => A y l b) i x
  rw [coordinateDerivative_sum (f := fun l y => B a l * A y l b)
    (fun l => (differentiableAt_const (c := B a l)).mul
    ((contDiff_matrix_entry hA l b).differentiable (by norm_num) x))]
  apply Finset.sum_congr rfl
  intro l _
  change coordinateDerivative (B a l • (fun y => A y l b)) i x = _
  exact coordinateDerivative_smul ((contDiff_matrix_entry hA l b).differentiable (by norm_num) x) _ _

lemma hessianMetricDiffusionMatrix_const_mul (φ V : Space n → ℝ)
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} (hA : ContDiff ℝ 2 A)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    hessianMetricDiffusionMatrix φ V (fun y => B * A y) x = B * hessianMetricDiffusionMatrix φ V A x := by
  ext a b
  change hessianMetricDiffusion φ V (fun y => ∑ l, B a l * A y l b) x =
    ∑ l, B a l * hessianMetricDiffusion φ V (fun y => A y l b) x
  rw [hessianMetricDiffusion_sum _ _ (fun l => contDiff_const.mul (contDiff_matrix_entry hA l b))]
  apply Finset.sum_congr rfl
  intro l _
  change hessianMetricDiffusion φ V (B a l • (fun y => A y l b)) x = _
  exact hessianMetricDiffusion_smul _ _ (contDiff_matrix_entry hA l b) _ _

/-- The trace-product rule follows from the scalar product rule and finite
sum commutations, with the noncommuting matrix order preserved. -/
theorem hessianMetricDiffusion_trace_mul {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (V : Space n → ℝ)
    {A B : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (x : Space n) :
    hessianMetricDiffusion φ V (fun y => (A y * B y).trace) x =
      (A x * hessianMetricDiffusionMatrix φ V B x).trace +
      (hessianMetricDiffusionMatrix φ V A x * B x).trace +
      2 * ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        (coordinateDerivativeMatrix A i x * coordinateDerivativeMatrix B j x).trace := by
  change hessianMetricDiffusion φ V (fun y => ∑ a, ∑ b, A y a b * B y b a) x = _
  rw [hessianMetricDiffusion_sum _ _ (fun a => ContDiff.sum (fun b _ =>
    (contDiff_matrix_entry hA a b).mul (contDiff_matrix_entry hB b a)))]
  simp_rw [hessianMetricDiffusion_sum _ _ (fun b =>
    (contDiff_matrix_entry hA _ b).mul (contDiff_matrix_entry hB b _)),
    hessianMetricDiffusion_mul hφ V (contDiff_matrix_entry hA _ _)
      (contDiff_matrix_entry hB _ _), Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : (∑ a, ∑ b, A x a b * hessianMetricDiffusion φ V (fun y => B y b a) x) =
      (A x * hessianMetricDiffusionMatrix φ V B x).trace := rfl
  have hsecond : (∑ a, ∑ b, B x b a * hessianMetricDiffusion φ V (fun y => A y a b) x) =
      (hessianMetricDiffusionMatrix φ V A x * B x).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hessianMetricDiffusionMatrix, mul_comm]
  rw [hfirst, hsecond]
  congr 2
  unfold hessianMetricGradientPair
  change (∑ a, ∑ b, ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      coordinateDerivative (fun y => A y a b) i x * coordinateDerivative (fun y => B y b a) j x) =
    ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      (∑ a, ∑ b, coordinateDerivative (fun y => A y a b) i x * coordinateDerivative (fun y => B y b a) j x)
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

theorem hessianMetricDiffusion_trace_square {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (V : Space n → ℝ)
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} (hA : ContDiff ℝ 2 A) (x : Space n) :
    hessianMetricDiffusion φ V (fun y => (A y * A y).trace) x =
      2 * (A x * hessianMetricDiffusionMatrix φ V A x).trace +
      2 * ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        (coordinateDerivativeMatrix A i x * coordinateDerivativeMatrix A j x).trace := by
  rw [hessianMetricDiffusion_trace_mul hφ V hA hA,
    Matrix.trace_mul_comm (hessianMetricDiffusionMatrix φ V A x) (A x)]
  ring

end KLS
end

#print axioms KLS.hessianMetricDiffusionMatrix_const_mul
#print axioms KLS.hessianMetricDiffusion_trace_mul
#print axioms KLS.hessianMetricDiffusion_trace_square
