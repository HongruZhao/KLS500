import KLS.MomentMapMaximumPrinciple

/-!
# Global Hessian bound derived from uniform target convexity

Penalized finite differences supply a bound independent of the penalty.
The penalty tends to zero, followed by the difference scale. No global
bound for the source Hessian is a hypothesis.
-/

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped Topology ContDiff NNReal BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma exists_bound_radial_target_derivative {φ V : Space n → ℝ}
    (hV : ContDiff ℝ 1 V) (hb : Bornology.IsBounded (range (gradient φ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |fderiv ℝ V (gradient φ x) (gradient φ x)| ≤ C := by
  have hd : Continuous (fderiv ℝ V) :=
    (hV.fderiv_right (m := 0) (by norm_num)).continuous
  have hf : Continuous (fun y : Space n => fderiv ℝ V y y) := hd.clm_apply continuous_id
  obtain ⟨C, hC⟩ := (hb.isCompact_closure.image hf).isBounded.exists_norm_le
  have hbound (x : Space n) : |fderiv ℝ V (gradient φ x) (gradient φ x)| ≤ C := by
    exact hC _ (mem_image_of_mem _ (subset_closure (mem_range_self x)))
  exact ⟨C, (abs_nonneg _).trans (hbound 0), hbound⟩

lemma le_linear_add_sqrt_of_quadratic {κ r b u : ℝ}
    (hκ : 0 < κ) (hr : 0 ≤ r) (hb : 0 ≤ b) (_hu : 0 ≤ u)
    (hquad : κ * u ^ 2 ≤ 2 * r * u + b) :
    u ≤ 2 * r / κ + Real.sqrt (b / κ) := by
  let a := 2 * r / κ
  let z := Real.sqrt (b / κ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzs : z ^ 2 = b / κ := Real.sq_sqrt (by positivity)
  have hak : κ * a = 2 * r := by dsimp [a]; field_simp
  have hzk : κ * z ^ 2 = b := by rw [hzs]; field_simp
  have hq : u ^ 2 ≤ a * u + z ^ 2 := by
    apply (mul_le_mul_iff_right₀ hκ).mp
    calc
      κ * u ^ 2 ≤ 2 * r * u + b := hquad
      _ = κ * (a * u + z ^ 2) := by rw [mul_add, ← mul_assoc, hak, hzk]
  change u ≤ a + z
  by_contra hh
  have hh' : a + z < u := lt_of_not_ge hh
  have hpos : 0 < (u - (a + z)) * (u + z) := by
    apply mul_pos (sub_pos.mpr hh')
    linarith
  nlinarith [mul_nonneg ha hz]

/-- Actual unscaled finite differences satisfy the contraction estimate. -/
theorem symmetricSecondDifference_le_of_uniformlyConvex_target {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hφc : ConvexOn ℝ univ φ)
    (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hb : Bornology.IsBounded (range (gradient φ))) (h x : Space n) :
    symmetricSecondDifference φ h x ≤ 4 * ‖h‖ ^ 2 / κ := by
  obtain ⟨R, hR⟩ := lipschitzWith_of_bounded_gradient (hφ.differentiable (by norm_num)) hb
  obtain ⟨xmin, hmin⟩ := exists_minimizer_of_finite_potentialMeasure hφ.continuous hφc
  obtain ⟨C, hC, hbound⟩ := exists_bound_radial_target_derivative hV hb
  have hreg (η : ℝ) (hη : 0 < η) :
      symmetricSecondDifference φ h x ≤ 4 * ‖h‖ ^ 2 / κ +
        2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) + η * (φ x - φ xmin) := by
    obtain ⟨y, hy⟩ := exists_maximizer_penalizedSecondDifference hφ.continuous hφc hR h hη
    obtain ⟨hd, hu⟩ := strongConvex_secondDifference_maximum_estimates hφ hφc
      (hV.differentiable (by norm_num)) hVc hstrong hpos hMA hbound h hη.le y hy
    let u := ‖(1 / 2 : ℝ) • (gradient φ (y + h) - gradient φ (y - h))‖
    have hubound : u ≤ 2 * ‖h‖ / κ + Real.sqrt (η * ((n : ℝ) + C) / κ) :=
      le_linear_add_sqrt_of_quadratic hκ (norm_nonneg h) (by positivity)
        (norm_nonneg _) (hu.trans (add_le_add hd le_rfl))
    have hd' : symmetricSecondDifference φ h y ≤ 4 * ‖h‖ ^ 2 / κ +
        2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) := by
      have hh := hd.trans (mul_le_mul_of_nonneg_left hubound (by positivity : 0 ≤ 2 * ‖h‖))
      convert hh using 1
      ring
    have hxy := hy x
    have hmy := mul_le_mul_of_nonneg_left (hmin y) hη.le
    linarith
  have heta := cutoffScale_tendsto_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((heta.mul_const ((n : ℝ) + C)).div_const κ)
  have hlim := (((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => 4 * ‖h‖ ^ 2 / κ) atTop (𝓝 (4 * ‖h‖ ^ 2 / κ))).add
      (hs.const_mul (2 * ‖h‖))).add
    (heta.mul_const (φ x - φ xmin)))
  have hlim' : Tendsto (fun k => 4 * ‖h‖ ^ 2 / κ +
      2 * ‖h‖ * Real.sqrt (cutoffScale k * ((n : ℝ) + C) / κ) +
      cutoffScale k * (φ x - φ xmin)) atTop (𝓝 (4 * ‖h‖ ^ 2 / κ)) := by
    simpa only [zero_mul, zero_div, Real.sqrt_zero, mul_zero, add_zero, Function.comp_def] using hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall fun k => hreg _ (cutoffScale_pos k))

/-- The second directional derivative bound is obtained by an actual Taylor
limit of the just-proved finite differences. -/
theorem secondFrechet_le_of_uniformlyConvex_target {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hφc : ConvexOn ℝ univ φ)
    (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hb : Bornology.IsBounded (range (gradient φ))) (x v : Space n) :
    fderiv ℝ (fderiv ℝ φ) x v v ≤ (4 / κ) * ‖v‖ ^ 2 := by
  apply le_of_tendsto (tendsto_symmetricSecondDifference_directional hφ x v)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hh := symmetricSecondDifference_le_of_uniformlyConvex_target hφ hφc hV hVc hκ
    hstrong hpos hMA hb (t • v) x
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht0)).mpr
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
  convert hh using 1
  ring

lemma posDef_entry_abs_le_of_diag_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {C : ℝ} (hC : 0 ≤ C) (hdiag : ∀ i, A i i ≤ C)
    (i j : Fin n) : |A i j| ≤ C := by
  have hcs : (A i j) ^ 2 ≤ A i i * A j j := by
    simpa [pow_two] using hA.star_dotProduct_mulVec_mul_le (Pi.single i 1) (Pi.single j 1)
  have hp : A i i * A j j ≤ C ^ 2 := by
    have hh := mul_le_mul (hdiag i) (hdiag j) (hA.posSemidef.diag_nonneg : 0 ≤ A j j) hC
    simpa only [pow_two] using hh
  apply (sq_le_sq₀ (abs_nonneg _) hC).mp
  rw [sq_abs]
  exact hcs.trans hp

/-- The actual coordinate Hessian has bounded range. This supplies the
formerly assumed global Hessian-bound hypothesis from uniform target
convexity and genuine smooth Monge--Ampère data. -/
theorem bounded_hessian_of_uniformlyConvex_target {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hφc : ConvexOn ℝ univ φ)
    (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hb : Bornology.IsBounded (range (gradient φ))) :
    Bornology.IsBounded (range (coordinateHessian φ)) := by
  have hC : 0 ≤ 4 / κ := by positivity
  have hdiag (x : Space n) (i : Fin n) : coordinateHessian φ x i i ≤ 4 / κ := by
    have hh := secondFrechet_le_of_uniformlyConvex_target hφ hφc hV hVc hκ
      hstrong hpos hMA hb x (EuclideanSpace.single i 1)
    rw [coordinateHessian_eq_fderiv_fderiv
      ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
    simpa only [PiLp.norm_single, Real.norm_eq_abs, abs_one, one_pow, mul_one] using hh
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨4 / κ, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply (Matrix.norm_le_iff hC).mpr
  intro i j
  simpa only [Real.norm_eq_abs] using
    posDef_entry_abs_le_of_diag_le (hpos x) hC (hdiag x) i j

end KLS
end

#print axioms KLS.symmetricSecondDifference_le_of_uniformlyConvex_target
#print axioms KLS.secondFrechet_le_of_uniformlyConvex_target
#print axioms KLS.bounded_hessian_of_uniformlyConvex_target
