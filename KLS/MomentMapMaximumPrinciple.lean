import KLS.MomentMapFiniteDifference
import KLS.MatrixLogDetTangent
import KLS.HessianMetricEvolution
import KLS.MatrixTracePositive
import KLS.WeightedDiffusionLinear
import KLS.SmoothCutoffSequence

/-! Penalized finite-difference maximum calculations for the actual
Monge--Ampere equation. These estimates do not assume a global Hessian bound. -/

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateHessian_neg_posSemidef_at_global_max {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (x : Space n) (hmax : ∀ y, F y ≤ F x) :
    (-coordinateHessian F x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_symmetric hF x).neg
  · intro w
    have hh := secondFrechet_nonpos_at_global_max hF x hmax (WithLp.toLp 2 w)
    rw [← coordinateHessian_quadratic_eq hF] at hh
    have he : star w ⬝ᵥ ((-coordinateHessian F x) *ᵥ w) =
        -(∑ i : Fin n, ∑ j : Fin n, coordinateHessian F x i j * w i * w j) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.neg_apply,
        Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact neg_nonneg.mpr hh

lemma trace_mul_hessian_nonpos_at_global_max {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (x : Space n) (hmax : ∀ y, F y ≤ F x)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.PosSemidef) :
    (J * coordinateHessian F x).trace ≤ 0 := by
  have hh := trace_mul_nonneg_of_posSemidef hJ
    (coordinateHessian_neg_posSemidef_at_global_max hF x hmax)
  simpa only [Matrix.mul_neg, Matrix.trace_neg, neg_nonneg] using hh

lemma coordinateDerivative_translate {F : Space n → ℝ}
    (hF : Differentiable ℝ F) (a : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => F (y + a)) i x = coordinateDerivative F i (x + a) := by
  have hh := (hF (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
  unfold coordinateDerivative
  rw [show fderiv ℝ (fun y => F (y + a)) x = fderiv ℝ F (x + a) from by
    convert! hh.fderiv using 1]

lemma coordinateHessian_translate {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (a x : Space n) :
    coordinateHessian (fun y => F (y + a)) x = coordinateHessian F (x + a) := by
  ext i j
  have he : coordinateDerivative (fun y => F (y + a)) j =
      fun y => coordinateDerivative F j (y + a) := by
    funext y
    exact coordinateDerivative_translate (hF.differentiable (by norm_num)) a j y
  unfold coordinateHessian
  rw [he]
  exact coordinateDerivative_translate
    ((contDiff_coordinateDerivative hF (m := 1) (by norm_num) j).differentiable (by norm_num)) a i x

lemma coordinateHessian_symmetricSecondDifference {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h x : Space n) :
    coordinateHessian (symmetricSecondDifference φ h) x =
      coordinateHessian φ (x + h) + coordinateHessian φ (x - h) -
        (2 : ℝ) • coordinateHessian φ x := by
  have hp : ContDiff ℝ 2 (fun y => φ (y + h)) := by fun_prop
  have hm : ContDiff ℝ 2 (fun y => φ (y - h)) := by fun_prop
  have he : symmetricSecondDifference φ h =
      fun y => ((fun z => φ (z + h)) + (fun z => φ (z - h))) y - ((2 : ℝ) • φ) y := rfl
  ext i j
  rw [he, coordinateHessian_sub
    (f := (fun z => φ (z + h)) + (fun z => φ (z - h)))
    (g := (2 : ℝ) • φ) (hp.add hm) (by convert! hφ.const_smul (2 : ℝ)),
    coordinateHessian_add hp hm, coordinateHessian_smul hφ]
  have hmn : (fun y => φ (y - h)) = fun y => φ (y + (-h)) := by
    ext y
    rw [sub_eq_add_neg]
  rw [coordinateHessian_translate hφ, hmn, coordinateHessian_translate hφ]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    sub_eq_add_neg]

lemma elliptic_secondDifference_le_at_penalized_max {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (h : Space n) (η : ℝ) (x : Space n)
    (hmax : ∀ y, symmetricSecondDifference φ h y - η * φ y ≤
      symmetricSecondDifference φ h x - η * φ x) :
    ((coordinateHessian φ x)⁻¹ * coordinateHessian (symmetricSecondDifference φ h) x).trace ≤
      η * n := by
  have hD := symmetricSecondDifference_contDiff hφ h
  have hF : ContDiff ℝ 2 (fun y => symmetricSecondDifference φ h y - η * φ y) :=
    hD.sub (contDiff_const.mul hφ)
  have hh := trace_mul_hessian_nonpos_at_global_max hF x hmax (hpos x).inv.posSemidef
  have he : coordinateHessian (fun y => symmetricSecondDifference φ h y - η * φ y) x =
      coordinateHessian (symmetricSecondDifference φ h) x - η • coordinateHessian φ x := by
    ext i j
    rw [coordinateHessian_sub hD (contDiff_const.mul hφ)]
    change _ = _ - η * coordinateHessian φ x i j
    congr 1
    exact coordinateHessian_smul hφ η x i j
  rw [he, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hpos x).det_pos.ne'),
    Matrix.trace_smul, Matrix.trace_one] at hh
  simpa only [Fintype.card_fin, smul_eq_mul] using sub_nonpos.mp hh

lemma secondDifference_target_le_at_penalized_max {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (h : Space n) (η : ℝ) (x : Space n)
    (hmax : ∀ y, symmetricSecondDifference φ h y - η * φ y ≤
      symmetricSecondDifference φ h x - η * φ x) :
    symmetricSecondDifference (fun y => V (gradient φ y)) h x ≤
      symmetricSecondDifference φ h x + η * n := by
  have hp := log_det_tangent_bound (hpos x) (hpos (x + h))
  have hm := log_det_tangent_bound (hpos x) (hpos (x - h))
  have ht := elliptic_secondDifference_le_at_penalized_max hφ hpos h η x hmax
  rw [coordinateHessian_symmetricSecondDifference hφ, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hpos x).det_pos.ne'),
    Matrix.trace_smul, Matrix.trace_one] at ht
  simp only [Fintype.card_fin, smul_eq_mul] at ht
  rw [hMA (x + h), hMA x] at hp
  rw [hMA (x - h), hMA x] at hm
  unfold symmetricSecondDifference
  linarith

/-- Uniform convexity supplies the genuine midpoint gap of the target
potential. The coefficient uses V - κ‖·‖²/2. -/
lemma target_strongConvex_midpoint {V : Space n → ℝ} {κ : ℝ}
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (m u : Space n) :
    κ * ‖u‖ ^ 2 ≤ V (m + u) + V (m - u) - 2 * V m := by
  have hh := hstrong.2 (mem_univ (m + u)) (mem_univ (m - u))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • (m + u) + (1 / 2 : ℝ) • (m - u) = m := by module
  rw [he] at hh
  dsimp only at hh
  rw [norm_add_sq_real, norm_sub_sq_real] at hh
  simp only [smul_eq_mul] at hh
  nlinarith

lemma target_gap_lower_at_penalized_max {φ V : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (h : Space n) (η : ℝ) (x : Space n)
    (hmax : ∀ y, symmetricSecondDifference φ h y - η * φ y ≤
      symmetricSecondDifference φ h x - η * φ x) :
    κ * ‖(1 / 2 : ℝ) • (gradient φ (x + h) - gradient φ (x - h))‖ ^ 2 +
      η * fderiv ℝ V (gradient φ x) (gradient φ x) ≤
      symmetricSecondDifference (fun y => V (gradient φ y)) h x := by
  let vp := gradient φ (x + h)
  let vm := gradient φ (x - h)
  let v := gradient φ x
  let m := (1 / 2 : ℝ) • (vp + vm)
  let u := (1 / 2 : ℝ) • (vp - vm)
  have hp : m + u = vp := by dsimp [m, u]; module
  have hm : m - u = vm := by dsimp [m, u]; module
  have hgap := target_strongConvex_midpoint hstrong m u
  rw [hp, hm] at hgap
  have hsupport := convex_supporting_fderiv hVc hV v m
  have hgrad := gradient_symmetricSecondDifference_at_penalized_max hφ h η x hmax
  have hmv : m - v = (η / 2) • v := by
    calc
      m - v = (1 / 2 : ℝ) • (vp + vm - (2 : ℝ) • v) := by dsimp [m]; module
      _ = (1 / 2 : ℝ) • (η • v) := by rw [hgrad]
      _ = (η / 2) • v := by module
  rw [hmv, map_smul, smul_eq_mul] at hsupport
  change κ * ‖u‖ ^ 2 + η * fderiv ℝ V v v ≤ V vp + V vm - 2 * V v
  linarith

/-- Two-sided numerical bounds at the constructed penalized maximum. All
PDE and maximum-principle statements are derived above for the actual
potential. C bounds the target radial derivative only on the source gradient
range and is independent of the penalty and finite-difference scale. -/
theorem strongConvex_secondDifference_maximum_estimates {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : ConvexOn ℝ univ φ)
    (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient φ x) (gradient φ x)| ≤ C)
    (h : Space n) {η : ℝ} (hη : 0 ≤ η) (x : Space n)
    (hmax : ∀ y, symmetricSecondDifference φ h y - η * φ y ≤
      symmetricSecondDifference φ h x - η * φ x) :
    let u := (1 / 2 : ℝ) • (gradient φ (x + h) - gradient φ (x - h))
    symmetricSecondDifference φ h x ≤ 2 * ‖h‖ * ‖u‖ ∧
      κ * ‖u‖ ^ 2 ≤ symmetricSecondDifference φ h x + η * (n + C) := by
  dsimp only
  have hd := hφ.differentiable (by norm_num)
  constructor
  · have hh := (symmetricSecondDifference_le_gradient_difference hφc hd h x).trans
      ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
    have hu : ‖(1 / 2 : ℝ) • (gradient φ (x + h) - gradient φ (x - h))‖ =
        (1 / 2 : ℝ) * ‖gradient φ (x + h) - gradient φ (x - h)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [hu]
    nlinarith
  · have hlo := target_gap_lower_at_penalized_max hd hV hVc hstrong h η x hmax
    have hhi := secondDifference_target_le_at_penalized_max hφ hpos hMA h η x hmax
    have hb := (neg_abs_le (fderiv ℝ V (gradient φ x) (gradient φ x))).trans'
      (neg_le_neg (hC x))
    have hb' := mul_le_mul_of_nonneg_left hb hη
    linarith

end KLS
end

#print axioms KLS.elliptic_secondDifference_le_at_penalized_max
#print axioms KLS.secondDifference_target_le_at_penalized_max
#print axioms KLS.strongConvex_secondDifference_maximum_estimates
