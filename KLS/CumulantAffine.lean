import KLS.CumulantApriori
import KLS.AffineMomentMapStein

/-! Exact affine transport of actual cumulants of order at least two. -/
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS
variable {n m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem tiltLogLaplace_affineMatrixMeasure (hμ : IsCompact μ.support)
    (A : Matrix (Fin n) (Fin n) ℝ) (b z : Space n) :
    tiltLogLaplace (affineMatrixMeasure μ A b) z =
      inner ℝ z b + tiltLogLaplace μ (matrixAction A.transpose z) := by
  unfold tiltLogLaplace tiltPartition affineMatrixMeasure
  rw [integral_map (affineMatrixMap A b).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Space n => Real.exp (inner ℝ z x)) _ from by fun_prop)]
  have he (x : Space n) : Real.exp (inner ℝ z (affineMatrixMap A b x)) =
      Real.exp (inner ℝ z b) * Real.exp (inner ℝ (matrixAction A.transpose z) x) := by
    have ht : inner ℝ z (matrixAction A x) = inner ℝ (matrixAction A.transpose z) x := by
      calc
        _ = inner ℝ (matrixAction A x) z := real_inner_comm _ _
        _ = inner ℝ x (matrixAction A.transpose z) := inner_matrixAction_transpose A x z
        _ = _ := real_inner_comm _ _
    rw [affineMatrixMap_apply, inner_add_right, ht, Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul, Real.log_mul (Real.exp_ne_zero _) ?_, Real.log_exp]
  exact (tiltPartition_pos hμ (q := fun x => inner ℝ (matrixAction A.transpose z) x)
    (by fun_prop)).ne'

lemma iteratedFDeriv_clm_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hm : 2 ≤ m) (x : E) : iteratedFDeriv ℝ m L x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 2 k]
  ext h
  rw [iteratedFDeriv_succ_apply_right]
  have hd : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  rw [hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
  rfl

theorem cumulantTensor_affineMatrixMeasure (hμ : IsCompact μ.support) (hm : 2 ≤ m)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (h : Fin m → Space n) :
    cumulantTensor (affineMatrixMeasure μ A b) m h =
      cumulantTensor μ m (fun j => matrixAction A.transpose (h j)) := by
  have he : tiltLogLaplace (affineMatrixMeasure μ A b) =
      (fun z => inner ℝ z b) + tiltLogLaplace μ ∘ matrixAction A.transpose :=
    funext (tiltLogLaplace_affineMatrixMeasure hμ A b)
  have hlin : (fun z : Space n => inner ℝ z b) = innerSL ℝ b := by
    funext z
    exact real_inner_comm b z
  unfold cumulantTensor
  rw [he, iteratedFDeriv_add_apply (by rw [hlin]; exact (innerSL ℝ b).contDiff.contDiffAt)
    (((contDiff_tiltLogLaplace hμ).comp (matrixAction A.transpose).contDiff).contDiffAt.of_le (by simp)),
    hlin, iteratedFDeriv_clm_eq_zero _ hm, zero_add,
    (matrixAction A.transpose).iteratedFDeriv_comp_right (contDiff_tiltLogLaplace hμ) 0 (by simp)]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]

end KLS
end
#print axioms KLS.cumulantTensor_affineMatrixMeasure
