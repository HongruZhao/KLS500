import KLS.HessianTraceEvolution
import KLS.HessianMetricIntegrationExtension

/-!
# Integrability and the exact Hessian trace-moment identity

Boundedness of the actual Hessian supplies boundedness of the trace test.
The proved A.5 extension then permits integration of its actual evolution.
Each nonnegative term is proved integrable before the identity is split.
-/

open Matrix InnerProductSpace MeasureTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma contDiff_hessianTraceSquare {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (B : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ 2 (hessianTraceSquare φ B) := by
  have hA := contDiff_matrix_const_mul (contDiff_coordinateHessian_matrix hφ) B
  have heq : hessianTraceSquare φ B =
      fun y => ∑ i, ∑ j, (B * coordinateHessian φ y) i j * (B * coordinateHessian φ y) j i := by
    funext y
    change (B * coordinateHessian φ y * B * coordinateHessian φ y).trace =
      ((B * coordinateHessian φ y) * (B * coordinateHessian φ y)).trace
    simp only [Matrix.mul_assoc]
  rw [heq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_matrix_entry hA i j).mul (contDiff_matrix_entry hA j i)))

lemma exists_bound_hessianTraceSquare {φ : Space n → ℝ}
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (B : Matrix (Fin n) (Fin n) ℝ) : ∃ C : ℝ, ∀ x, ‖hessianTraceSquare φ B x‖ ≤ C := by
  have hF : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => (B * M * B * M).trace) :=
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul
      continuous_id).matrix_trace
  obtain ⟨C, hC⟩ := hH.isCompact_closure.bddAbove_image hF.norm.continuousOn
  exact ⟨C, fun x => hC ⟨coordinateHessian φ x, subset_closure ⟨x, rfl⟩, rfl⟩⟩

lemma continuous_hessianTrace_evolution_terms {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (hessianTraceGradientTerm φ B) ∧ Continuous (hessianTraceTargetTerm φ V B) ∧
      Continuous (hessianTraceThirdTerm φ B) := by
  have hH := (contDiff_coordinateHessian_matrix hφ).continuous
  have hJ := (contDiff_inverseHessian hφ hpos).continuous
  have hT (i : Fin n) : Continuous (fun x => hessianDerivative φ x i) := by
    apply continuous_matrix
    intro a b
    exact (contDiff_coordinateDerivative (contDiff_coordinateHessian hφ (m := 2)
      (by norm_num) a b) (m := 0) (by norm_num) i).continuous
  have hVh : Continuous (fun x => coordinateHessian V (gradient φ x)) := by
    apply continuous_matrix
    intro a b
    exact (contDiff_coordinateHessian hV (m := 0) (by norm_num) a b).continuous.comp
      (contDiff_gradient hφ (m := 0) (by norm_num)).continuous
  have hQ : Continuous (fun x => matrixTraceGram (coordinateHessian φ x)⁻¹ (hessianDerivative φ x)) := by
    apply continuous_matrix
    intro i j
    exact (((hJ.matrix_mul (hT i)).matrix_mul hJ).matrix_mul (hT j)).matrix_trace
  refine ⟨?_, ?_, ?_⟩
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (hJ.matrix_elem i j).mul
      ((((continuous_const.matrix_mul (hT i)).matrix_mul continuous_const).matrix_mul (hT j)).matrix_trace)
  · exact (((continuous_const.matrix_mul hH).matrix_mul continuous_const).matrix_mul
      ((hH.matrix_mul hVh).matrix_mul hH)).matrix_trace
  · exact (((continuous_const.matrix_mul hH).matrix_mul continuous_const).matrix_mul hQ).matrix_trace

/-- The exact integrated equation (2.11), with all four terms genuinely L¹.
Neither the identity nor integrability of any third-derivative expression
is assumed. -/
theorem hessianTrace_moment_identity {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    Integrable (hessianTraceSquare φ B) (potentialMeasure φ) ∧
      Integrable (hessianTraceGradientTerm φ B) (potentialMeasure φ) ∧
      Integrable (hessianTraceTargetTerm φ V B) (potentialMeasure φ) ∧
      Integrable (hessianTraceThirdTerm φ B) (potentialMeasure φ) ∧
      (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) =
        (∫ x, hessianTraceGradientTerm φ B x ∂potentialMeasure φ) +
        (∫ x, hessianTraceTargetTerm φ V B x ∂potentialMeasure φ) +
        (∫ x, hessianTraceThirdTerm φ B x ∂potentialMeasure φ) := by
  have hS := contDiff_hessianTraceSquare hφ B
  obtain ⟨C, hC⟩ := exists_bound_hessianTraceSquare hH B
  have hSi : Integrable (hessianTraceSquare φ B) (potentialMeasure φ) :=
    (integrable_const C).mono' hS.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  obtain ⟨hLi, hLzero⟩ := integrable_hessianMetricDiffusion_and_integral_eq_zero
    hφ hV hφconv hpos hMA hgrad hS hC
    (hessianMetricDiffusion_hessianTraceSquare_add_nonneg hφ hV hVconv hpos hMA hB)
  have hsum : Integrable (fun x => hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
      hessianTraceThirdTerm φ B x) (potentialMeasure φ) := by
    convert! (hLi.add (hSi.const_mul 2)).const_mul (1 / 2 : ℝ) using 1
    funext x
    have heq := hessianMetricDiffusion_hessianTraceSquare hφ hV hpos hMA B x
    change hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
      hessianTraceThirdTerm φ B x = (1 / 2 : ℝ) *
        (hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x)
    linarith
  have hn (x : Space n) := hessianTrace_evolution_terms_nonneg
    (hφ.of_le (by norm_num)) hV hVconv hpos hB x
  obtain ⟨hAc, hDc, hCc⟩ := continuous_hessianTrace_evolution_terms hφ hV hpos B
  have hAi : Integrable (hessianTraceGradientTerm φ B) (potentialMeasure φ) := by
    apply hsum.mono' hAc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).1]
    linarith [(hn x).2.1, (hn x).2.2]
  have hDi : Integrable (hessianTraceTargetTerm φ V B) (potentialMeasure φ) := by
    apply hsum.mono' hDc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).2.1]
    linarith [(hn x).1, (hn x).2.2]
  have hCi : Integrable (hessianTraceThirdTerm φ B) (potentialMeasure φ) := by
    apply hsum.mono' hCc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hn x).2.2]
    linarith [(hn x).1, (hn x).2.1]
  refine ⟨hSi, hAi, hDi, hCi, ?_⟩
  have heq : (∫ x, hessianMetricDiffusion φ V (hessianTraceSquare φ B) x + 2 * hessianTraceSquare φ B x
      ∂potentialMeasure φ) = ∫ x, 2 * (hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x +
        hessianTraceThirdTerm φ B x) ∂potentialMeasure φ := by
    apply integral_congr_ae
    exact Eventually.of_forall (hessianMetricDiffusion_hessianTraceSquare hφ hV hpos hMA B)
  rw [integral_add hLi (hSi.const_mul 2), integral_const_mul, hLzero,
    integral_const_mul, integral_add
      (f := fun x => hessianTraceGradientTerm φ B x + hessianTraceTargetTerm φ V B x)
      (g := hessianTraceThirdTerm φ B) (hAi.add hDi) hCi, integral_add hAi hDi] at heq
  linarith

end KLS
end

#print axioms KLS.exists_bound_hessianTraceSquare
#print axioms KLS.hessianTrace_moment_identity
