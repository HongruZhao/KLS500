import KLS.WeakMomentCompactTransfer

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Translation commutes with the actual total coordinate derivative, even
 at exceptional points where the total derivative convention is used. -/
theorem coordinateDerivative_translate_total (f : Space n → ℝ) (h : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => f (y + h)) i x = coordinateDerivative f i (x + h) := by
  unfold coordinateDerivative
  rw [fderiv_comp_add_right]

/-- Actual first derivatives of the centered difference are the centered
 differences of the actual first derivatives. -/
theorem coordinateDerivative_symmetricSecondDifference_C1
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (h : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (symmetricSecondDifference u h) i x =
      coordinateDerivative u i (x + h)+coordinateDerivative u i (x - h)-2*coordinateDerivative u i x := by
  simp only [coordinateDerivative_eq_gradient,gradient_symmetricSecondDifference hu,
    PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]

/-- The genuine centered difference of a C1,1 scalar function has a globally
 Lipschitz actual gradient with four times the original constant. -/
theorem lipschitz_gradient_symmetricSecondDifference
    {u : Space n → ℝ} {G : ℝ≥0} (hu : Differentiable ℝ u)
    (hG : LipschitzWith G (gradient u)) (h : Space n) :
    LipschitzWith (4*G) (gradient (symmetricSecondDifference u h)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp : ‖gradient u (x + h)-gradient u (y + h)‖ ≤ G*‖x-y‖ := by
    simpa using hG.norm_sub_le (x + h) (y + h)
  have hm : ‖gradient u (x - h)-gradient u (y - h)‖ ≤ G*‖x-y‖ := by
    simpa using hG.norm_sub_le (x - h) (y - h)
  have hz := hG.norm_sub_le x y
  have he : gradient (symmetricSecondDifference u h) x-gradient (symmetricSecondDifference u h) y =
      ((gradient u (x + h)-gradient u (y + h))+(gradient u (x - h)-gradient u (y - h))) -
        (2 : ℝ) • (gradient u x-gradient u y) := by
    rw [gradient_symmetricSecondDifference hu,gradient_symmetricSecondDifference hu]
    module
  rw [dist_eq_norm,he,dist_eq_norm]
  have ht := (norm_sub_le
    ((gradient u (x + h)-gradient u (y + h))+(gradient u (x - h)-gradient u (y - h)))
    ((2 : ℝ) • (gradient u x-gradient u y))).trans
      (add_le_add (norm_add_le (gradient u (x + h)-gradient u (y + h))
        (gradient u (x - h)-gradient u (y - h))) le_rfl)
  norm_num [norm_smul] at ht ⊢
  linarith

/-- At the three genuine coordinate-gradient derivative points, the actual
 Hessian of the centered difference is the centered actual Hessian. -/
theorem coordinateHessian_symmetricSecondDifference_at_C11
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (h x : Space n)
    (hz : ∀ j, DifferentiableAt ℝ (coordinateDerivative u j) x)
    (hp : ∀ j, DifferentiableAt ℝ (coordinateDerivative u j) (x + h))
    (hm : ∀ j, DifferentiableAt ℝ (coordinateDerivative u j) (x - h)) :
    coordinateHessian (symmetricSecondDifference u h) x =
      coordinateHessian u (x + h)+coordinateHessian u (x - h)-(2 : ℝ) • coordinateHessian u x := by
  ext i j
  have he : coordinateDerivative (symmetricSecondDifference u h) j =
      (fun y => coordinateDerivative u j (y + h)) + (fun y => coordinateDerivative u j (y - h)) -
        (2 : ℝ) • coordinateDerivative u j := by
    funext y
    exact coordinateDerivative_symmetricSecondDifference_C1 hu h j y
  have hplus : DifferentiableAt ℝ (fun y => coordinateDerivative u j (y + h)) x :=
    (differentiableAt_comp_add_right h).mpr (hp j)
  have hminus : DifferentiableAt ℝ (fun y => coordinateDerivative u j (y - h)) x := by
    simpa only [sub_eq_add_neg] using (differentiableAt_comp_add_right (-h)).mpr (by simpa only [← sub_eq_add_neg] using hm j)
  change coordinateDerivative (coordinateDerivative (symmetricSecondDifference u h) j) i x = _
  rw [he]
  have hsum : DifferentiableAt ℝ
      ((fun y => coordinateDerivative u j (y + h)) + (fun y => coordinateDerivative u j (y - h))) x :=
    hplus.add hminus
  have hscale : DifferentiableAt ℝ ((2 : ℝ) • coordinateDerivative u j) x := (hz j).const_smul 2
  change coordinateDerivative (fun y =>
    ((fun z => coordinateDerivative u j (z + h)) + (fun z => coordinateDerivative u j (z - h))) y -
      ((2 : ℝ) • coordinateDerivative u j) y) i x = _
  rw [coordinateDerivative_sub hsum hscale,coordinateDerivative_add hplus hminus,
    coordinateDerivative_smul (hz j),coordinateDerivative_translate_total]
  have hneg : coordinateDerivative (fun y => coordinateDerivative u j (y - h)) i x =
      coordinateDerivative (coordinateDerivative u j) i (x - h) := by
    simpa only [sub_eq_add_neg] using coordinateDerivative_translate_total (coordinateDerivative u j) (-h) i x
  rw [hneg]
  rfl

/-- For each fixed translation, the genuine centered Hessian identity holds
 almost everywhere by Rademacher and translation invariance of volume. -/
theorem coordinateHessian_symmetricSecondDifference_ae_C11
    {u : Space n → ℝ} {G : ℝ≥0} (hu : Differentiable ℝ u)
    (hG : LipschitzWith G (gradient u)) (h : Space n) :
    ∀ᵐ x ∂(volume : Measure (Space n)), coordinateHessian (symmetricSecondDifference u h) x =
      coordinateHessian u (x + h)+coordinateHessian u (x - h)-(2 : ℝ) • coordinateHessian u x := by
  have hAe : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ j, DifferentiableAt ℝ (coordinateDerivative u j) x :=
    ae_all_iff.mpr (fun j => (lipschitz_coordinateDerivative_of_gradient_lipschitz hG j).ae_differentiableAt (μ := volume))
  have hp := (measurePreserving_add_right (volume : Measure (Space n)) h).quasiMeasurePreserving.ae hAe
  have hm := (measurePreserving_add_right (volume : Measure (Space n)) (-h)).quasiMeasurePreserving.ae hAe
  filter_upwards [hAe,hp,hm] with x hz hx hy
  exact coordinateHessian_symmetricSecondDifference_at_C11 hu h x hz hx (by simpa only [sub_eq_add_neg] using hy)

end KLS
end
