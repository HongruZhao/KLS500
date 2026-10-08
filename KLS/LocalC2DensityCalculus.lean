import KLS.AveragedCofactorEllipticity

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma continuousOn_coordinateHessian_of_contDiffOn_two
    {u : Space n → ℝ} {S : Set (Space n)} (hS : IsOpen S) (hu : ContDiffOn ℝ 2 u S) :
    ContinuousOn (coordinateHessian u) S := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hD : ContDiffOn ℝ 1 (coordinateDerivative u j) S :=
    (hu.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  exact ((hD.fderiv_of_isOpen hS (m := 0) (by norm_num)).clm_apply contDiffOn_const).continuousOn

lemma contDiffOn_gradient_of_contDiffOn_two
    {u : Space n → ℝ} {S : Set (Space n)} (hS : IsOpen S) (hu : ContDiffOn ℝ 2 u S) :
    ContDiffOn ℝ 1 (gradient u) S :=
  (toDual ℝ (Space n)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hu.fderiv_of_isOpen hS (by norm_num))

/-- Smooth source and target weights give an actually C1 density once the
potential is actually C2. These hypotheses are not inferred from their
mere continuity in normalized weighted data. -/
theorem contDiffOn_weighted_density_of_c2
    {u W V : Space n → ℝ} {S : Set (Space n)} (hS : IsOpen S)
    (hu : ContDiffOn ℝ 2 u S) (hW : ContDiff ℝ 1 W) (hV : ContDiff ℝ 1 V) :
    ContDiffOn ℝ 1 (fun x => Real.exp (-W x + V (gradient u x))) S := by
  exact (hW.contDiffOn.neg.add (hV.comp_contDiffOn (contDiffOn_gradient_of_contDiffOn_two hS hu))).exp

lemma translatedDifferenceQuotient_bound_of_lipschitzOn
    {f : Space n → ℝ} {S : Set (Space n)} {L : ℝ≥0} (hf : LipschitzOnWith L f S)
    (v : Space n) (h : ℝ) {x : Space n} (hx : x ∈ S) (hxh : x + h • v ∈ S) :
    |translatedDifferenceQuotient f v h x| ≤ L * ‖v‖ := by
  by_cases hh : h = 0
  · simp only [hh, translatedDifferenceQuotient, _root_.inv_zero, zero_mul, abs_zero]
    positivity
  have hbound : |f (x + h • v) - f x| ≤ L * (|h| * ‖v‖) := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left,
      norm_smul] using hf.dist_le_mul _ hxh _ hx
  unfold translatedDifferenceQuotient
  rw [abs_mul, abs_inv]
  calc
    _ ≤ |h|⁻¹ * (L * (|h| * ‖v‖)) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = L * ‖v‖ := by field_simp

/-- On a compact convex set, the actual C1 density supplies a uniform
bound for every translated right-hand-side quotient. -/
theorem exists_bound_density_difference_quotients
    {u W V : Space n → ℝ} {S K : Set (Space n)} (hS : IsOpen S)
    (hu : ContDiffOn ℝ 2 u S) (hW : ContDiff ℝ 1 W) (hV : ContDiff ℝ 1 V)
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKS : K ⊆ S) :
    ∃ L : ℝ≥0, ∀ (v : Space n) (h : ℝ) (x : Space n), x ∈ K → x + h • v ∈ K →
      |translatedDifferenceQuotient (fun y => Real.exp (-W y + V (gradient u y))) v h x| ≤ L * ‖v‖ := by
  obtain ⟨L, hL⟩ := ((contDiffOn_weighted_density_of_c2 hS hu hW hV).mono hKS).exists_lipschitzOnWith
    (by norm_num) hKconv hK
  exact ⟨L, fun v h x hx hxh => translatedDifferenceQuotient_bound_of_lipschitzOn hL v h hx hxh⟩

end KLS
end
