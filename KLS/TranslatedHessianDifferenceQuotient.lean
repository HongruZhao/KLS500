import KLS.DeterminantChordIdentity

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The genuine translated difference quotient of the potential. -/
def translatedDifferenceQuotient (u : Space n → ℝ) (v : Space n) (h : ℝ) : Space n → ℝ :=
  fun x => h⁻¹ * (u (x + h • v) - u x)

lemma coordinateDerivative_comp_translation (u : Space n → ℝ) (a x : Space n) (i : Fin n) :
    coordinateDerivative (fun y => u (y + a)) i x = coordinateDerivative u i (x + a) := by
  simp only [coordinateDerivative, fderiv_comp_add_right]

lemma coordinateDerivative_translatedDifferenceQuotient_at
    {u : Space n → ℝ} (v : Space n) (h : ℝ) {x : Space n}
    (hx : DifferentiableAt ℝ u x) (hxh : DifferentiableAt ℝ u (x + h • v)) (i : Fin n) :
    coordinateDerivative (translatedDifferenceQuotient u v h) i x =
      h⁻¹ * (coordinateDerivative u i (x + h • v) - coordinateDerivative u i x) := by
  have htrans : DifferentiableAt ℝ (fun y => u (y + h • v)) x :=
    hxh.comp x ((differentiableAt_id).add_const _)
  change coordinateDerivative (h⁻¹ • (fun y => u (y + h • v) - u y)) i x = _
  rw [coordinateDerivative_smul (f := fun y => u (y + h • v) - u y) (htrans.sub hx), coordinateDerivative_sub htrans hx,
    coordinateDerivative_comp_translation]

lemma differentiableAt_coordinateDerivative_of_contDiffAt_two
    {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u x) (i : Fin n) :
    DifferentiableAt ℝ (coordinateDerivative u i) x :=
  ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)

/-- The quotient's actual Hessian is the quotient of the actual Hessians.
Only C2 at the two points and global first differentiability are used. -/
theorem coordinateHessian_translatedDifferenceQuotient
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (v : Space n) (h : ℝ) {x : Space n}
    (hx : ContDiffAt ℝ 2 u x) (hxh : ContDiffAt ℝ 2 u (x + h • v)) :
    coordinateHessian (translatedDifferenceQuotient u v h) x =
      h⁻¹ • (coordinateHessian u (x + h • v) - coordinateHessian u x) := by
  ext i j
  have heq : coordinateDerivative (translatedDifferenceQuotient u v h) j =
      translatedDifferenceQuotient (coordinateDerivative u j) v h := by
    funext y
    exact coordinateDerivative_translatedDifferenceQuotient_at v h (hu y) (hu (y + h • v)) j
  change coordinateDerivative (coordinateDerivative (translatedDifferenceQuotient u v h) j) i x = _
  rw [heq, coordinateDerivative_translatedDifferenceQuotient_at v h
    (differentiableAt_coordinateDerivative_of_contDiffAt_two hx j)
    (differentiableAt_coordinateDerivative_of_contDiffAt_two hxh j)]
  rfl

lemma contDiffAt_translatedDifferenceQuotient
    {u : Space n → ℝ} {m : ℕ∞ω} (v : Space n) (h : ℝ) {x : Space n}
    (hx : ContDiffAt ℝ m u x) (hxh : ContDiffAt ℝ m u (x + h • v)) :
    ContDiffAt ℝ m (translatedDifferenceQuotient u v h) x := by
  have htrans : ContDiffAt ℝ m (fun y => u (y + h • v)) x :=
    hxh.comp x (contDiffAt_id.add contDiffAt_const)
  exact contDiffAt_const.mul (htrans.sub hx)

/-- The nonlinear equation at two points gives the actual linear equation
for the translated potential quotient. No derivative of the Hessian is
assumed or taken in this exact identity. -/
theorem translated_difference_quotient_mongeAmpere
    {u f : Space n → ℝ} (hu : Differentiable ℝ u) (v : Space n) (h : ℝ) {x : Space n}
    (hx : ContDiffAt ℝ 2 u x) (hxh : ContDiffAt ℝ 2 u (x + h • v))
    (hposx : (coordinateHessian u x).PosDef)
    (hposxh : (coordinateHessian u (x + h • v)).PosDef)
    (hdetx : (coordinateHessian u x).det = f x)
    (hdetxh : (coordinateHessian u (x + h • v)).det = f (x + h • v)) :
    (averagedCofactor (coordinateHessian u x) (coordinateHessian u (x + h • v)) *
      coordinateHessian (translatedDifferenceQuotient u v h) x).trace =
        translatedDifferenceQuotient f v h x := by
  rw [coordinateHessian_translatedDifferenceQuotient hu v h hx hxh,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    ← determinant_chord_identity hposx hposxh, hdetx, hdetxh]
  rfl

end KLS
end
