import KLS.HessianTraceIntegration
import KLS.MomentMapIntegration

/-! # Actual bounded-Hessian moments and isotropic Hessian mean -/

open Matrix InnerProductSpace MeasureTheory Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma exists_bound_matrix_comp_of_bounded_range
    {A : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : Bornology.IsBounded (range A))
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ x, ‖F (A x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hA.isCompact_closure.bddAbove_image hF.norm.continuousOn
  exact ⟨C, fun x => hC ⟨A x, subset_closure ⟨x, rfl⟩, rfl⟩⟩

lemma memLp_matrix_comp_of_bounded_range {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] {A : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : Continuous A) (hAb : Bornology.IsBounded (range A))
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ} (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp (fun x => F (A x)) p (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := exists_bound_matrix_comp_of_bounded_range hAb hF
  exact MemLp.of_bound (hF.comp hA).aestronglyMeasurable C (Eventually.of_forall hC)

lemma momentMap_hessianMatrix_eq_coordinateHessian {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : Space n) :
    MomentMap.hessianMatrix φ x = coordinateHessian φ x := by
  ext i j
  change coordinateDerivative (fun y => gradient φ y i) j x = coordinateHessian φ x i j
  have heq : (fun y => gradient φ y i) = coordinateDerivative φ i := by
    funext y
    exact (coordinateDerivative_eq_gradient φ i y).symm
  rw [heq]
  exact (coordinateHessian_symmetric hφ x).apply i j

theorem memLp_coordinateHessian_entry_of_bounded {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ))) (i j : Fin n) :
    MemLp (fun x => coordinateHessian φ x i j) 2 (potentialMeasure φ) :=
  memLp_matrix_comp_of_bounded_range (φ := φ) (contDiff_coordinateHessian_matrix hφ).continuous hH
    (by fun_prop : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)) 2

/-- Isotropy is asserted of the actual gradient pushforward. The Hessian
entry's L¹ requirement is proved from the genuine bounded Hessian range. -/
theorem integral_coordinateHessian_entry_eq_one_of_isotropic {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 4 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ)) (i j : Fin n) :
    (∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have hHi := (memLp_coordinateHessian_entry_of_bounded hφ hH i j).integrable (by norm_num)
  have hMi : Integrable (fun x => MomentMap.hessianMatrix φ x i j) (potentialMeasure φ) := by
    simpa only [momentMap_hessianMatrix_eq_coordinateHessian (hφ.of_le (by norm_num))] using hHi
  simpa only [momentMap_hessianMatrix_eq_coordinateHessian (hφ.of_le (by norm_num))] using
    MomentMap.integral_hessian_entry_eq_one (hφ.differentiable (by norm_num))
      ((contDiff_gradient hφ (m := 1) (by norm_num)).differentiable (by norm_num)) hiso i j hMi

/-- Finite entrywise integration preserves actual fixed matrix congruences. -/
lemma integral_matrix_congruence_entry {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {H : α → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ a b, Integrable (fun x => H x a b) μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∫ x, (R * H x * R.transpose) i j ∂μ) =
      (R * Matrix.of (fun a b => ∫ x, H x a b ∂μ) * R.transpose) i j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ
    (fun a _ => ((hH a b).const_mul (R i a)).mul_const (R.transpose b j)))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum Finset.univ
    (fun a _ => ((hH a b).const_mul (R i a)).mul_const (R.transpose b j))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_mul_const, integral_const_mul]
  rfl

end KLS
end

#print axioms KLS.memLp_coordinateHessian_entry_of_bounded
#print axioms KLS.integral_coordinateHessian_entry_eq_one_of_isotropic
#print axioms KLS.integral_matrix_congruence_entry
