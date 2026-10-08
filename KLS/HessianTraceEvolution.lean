import KLS.HessianMetricMatrixProduct
import KLS.MatrixTracePositive
import KLS.ConvexHessian

/-!
# Actual evolution of Tr(B H B H)

The algebraic identity preserves matrix order and holds for arbitrary B.
Positivity of the three terms uses the stated PSD assumption on B and actual
convexity of V. No trace-evolution or positivity conclusion is assumed.
-/

open Matrix InnerProductSpace Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

def hessianTraceSquare (φ : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (B * coordinateHessian φ x * B * coordinateHessian φ x).trace

def hessianTraceGradientTerm (φ : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
    (B * hessianDerivative φ x i * B * hessianDerivative φ x j).trace

def hessianTraceTargetTerm (φ V : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : ℝ :=
  ((B * coordinateHessian φ x * B) *
    (coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x)).trace

def hessianTraceThirdTerm (φ : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ((B * coordinateHessian φ x * B) *
    matrixTraceGram (coordinateHessian φ x)⁻¹ (hessianDerivative φ x)).trace

lemma hessianMetricDiffusionMatrix_hessian {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x)) (x : Space n) :
    hessianMetricDiffusionMatrix φ V (coordinateHessian φ) x =
      -coordinateHessian φ x +
        coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x +
        matrixTraceGram (coordinateHessian φ x)⁻¹ (hessianDerivative φ x) := by
  ext i j
  have hi := hessianMetricDiffusion_hessian hφ hV hpos hMA x i j
  change hessianMetricDiffusion φ V (fun y => coordinateHessian φ y i j) x =
    -coordinateHessian φ x i j +
      (coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x) i j +
      ((coordinateHessian φ x)⁻¹ * hessianDerivative φ x i *
        (coordinateHessian φ x)⁻¹ * hessianDerivative φ x j).trace
  linarith

/-- Letwin's pointwise equation (2.10), derived from actual derivatives. -/
theorem hessianMetricDiffusion_hessianTraceSquare {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x =
      2 * (hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
        hessianTraceThirdTerm φ B x) := by
  have hH := contDiff_coordinateHessian_matrix hφ
  have heq : hessianTraceSquare φ B =
      fun y => ((B * coordinateHessian φ y) * (B * coordinateHessian φ y)).trace := by
    funext y
    simp only [hessianTraceSquare, Matrix.mul_assoc]
  rw [heq, hessianMetricDiffusion_trace_square (hφ.of_le (by norm_num)) V
    (contDiff_matrix_const_mul hH B)]
  simp_rw [hessianMetricDiffusionMatrix_const_mul φ V hH,
    coordinateDerivativeMatrix_const_mul hH]
  have hder (i : Fin n) : coordinateDerivativeMatrix (coordinateHessian φ) i x =
      hessianDerivative φ x i := rfl
  simp_rw [hder, hessianMetricDiffusionMatrix_hessian hφ hV hpos hMA]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg,
    hessianTraceGradientTerm, hessianTraceTargetTerm, hessianTraceThirdTerm, Matrix.mul_assoc]
  ring

theorem hessianTrace_evolution_terms_nonneg {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hV : ContDiff ℝ 2 V) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) (x : Space n) :
    0 ≤ hessianTraceGradientTerm φ B x ∧ 0 ≤ hessianTraceTargetTerm φ V B x ∧
      0 ≤ hessianTraceThirdTerm φ B x := by
  have hT (i : Fin n) := hessianDerivative_symmetric hφ x i
  have hBHB : (B * coordinateHessian φ x * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using (hpos x).posSemidef.conjTranspose_mul_mul_same B
  have hTarget : (coordinateHessian φ x * coordinateHessian V (gradient φ x) *
      coordinateHessian φ x).PosSemidef := by
    simpa only [(hpos x).isHermitian.eq] using
      (coordinateHessian_posSemidef_of_convex hV hVconv (gradient φ x)).conjTranspose_mul_mul_same
        (coordinateHessian φ x)
  exact ⟨inverse_weighted_traceGram_nonneg (hpos x).posSemidef.inv hB _ hT,
    trace_mul_nonneg_of_posSemidef hBHB hTarget,
    trace_mul_nonneg_of_posSemidef hBHB (matrixTraceGram_posSemidef (hpos x).posSemidef.inv _ hT)⟩

/-- The bounded-test subsolution premise is a conclusion for PSD B. -/
theorem hessianMetricDiffusion_hessianTraceSquare_add_nonneg {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) (x : Space n) :
    0 ≤ hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x := by
  rw [hessianMetricDiffusion_hessianTraceSquare hφ hV hpos hMA]
  obtain ⟨h1, h2, h3⟩ := hessianTrace_evolution_terms_nonneg (hφ.of_le (by norm_num)) hV hVconv hpos hB x
  positivity

end KLS
end

#print axioms KLS.hessianMetricDiffusion_hessianTraceSquare
#print axioms KLS.hessianTrace_evolution_terms_nonneg
#print axioms KLS.hessianMetricDiffusion_hessianTraceSquare_add_nonneg
