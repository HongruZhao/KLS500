import KLS.CompactDensityTransfer

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
open EllipticPdes.Regularity
variable {n : ℕ}

/-- Every compact set has one genuine volume L2 increment bound for all
 entries of the actual Hessian and every translation. The constant is
 constructed from weak transport and a smooth cutoff, not assumed energy. -/
theorem weak_moment_local_hessian_increment_bound
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space n, ∀ i j : Fin n,
      (∫ x in S, (coordinateHessian u (x+h) i j-coordinateHessian u x i j)^2) ≤ C*‖h‖^2 := by
  obtain ⟨η,hη,hη1,hη01⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hS isOpen_univ (subset_univ S)
  have hη2 : ContDiff ℝ 2 η := hη.1.of_le (by simp)
  have hη0 : ∀ x, 0 ≤ η x := fun x => (hη01 x).1
  have hηB : ∀ x, ‖η x‖ ≤ 1 := fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hη0 x)] using (hη01 x).2
  have hηS : ∀ x ∈ S, 1 ≤ η x := by
    intro x hx
    rw [hη1.self_of_nhdsSet x hx]
  obtain ⟨C,hC,hCbound⟩ := weak_moment_exists_compact_hessian_increment_bound
    hLip hc hV hVc hκ hstrong hK hKc hpush hη2 hη.2.1 hη0
  obtain ⟨B,hB,hBu⟩ := exists_compact_exp_potential_bound hLip.continuous hS
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro h i j
  let E : Space n → ℝ := fun x => (coordinateHessian u (x+h) i j-coordinateHessian u x i j)^2
  have hEi : Integrable E (potentialMeasure u) := by
    simpa only [add_zero,Pi.sub_apply] using
      ((memLp_translated_coordinateHessian_of_gradient_lipschitz hG (potentialMeasure u) h i j).sub
        (memLp_translated_coordinateHessian_of_gradient_lipschitz hG (potentialMeasure u) 0 i j)).integrable_sq
  have hE0 : ∀ x, 0 ≤ E x := fun _ => sq_nonneg _
  have hηEi : Integrable (fun x => η x*E x) (potentialMeasure u) :=
    hEi.bdd_mul hη2.continuous.aestronglyMeasurable (Eventually.of_forall hηB)
  have hp := integrable_frobenius_coordinateHessian_increment hG (potentialMeasure u) h
  have hm : Integrable (fun x => matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x))
      (potentialMeasure u) := by
    simpa only [sub_eq_add_neg] using integrable_frobenius_coordinateHessian_increment hG (potentialMeasure u) (-h)
  have hF := (hp.add hm).bdd_mul hη2.continuous.aestronglyMeasurable (Eventually.of_forall hηB)
  have hpoint (x : Space n) : η x*E x ≤
      η x*(matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
        matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x)) := by
    apply mul_le_mul_of_nonneg_left _ (hη0 x)
    exact (sq_entry_le_matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) i j).trans
      (le_add_of_nonneg_right (matrixFrobeniusSq_nonneg _))
  have hv := integral_restrict_le_potential_cutoff hLip.continuous hS hB hBu hEi hE0 hηEi hη0 hηS
  have hw := integral_mono hηEi hF hpoint
  have hh := hv.trans (mul_le_mul_of_nonneg_left (hw.trans (hCbound h)) hB)
  simpa only [E,mul_assoc] using hh

end KLS
end
