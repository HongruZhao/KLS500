import KLS.HessianMetricEvolution

/-!
# Divergence of the actual inverse Hessian

The genuine inverse derivative and the first differentiated Monge–Ampère
equation determine the drift of the inverse-Hessian diffusion. No
divergence or measure-symmetry identity is assumed.
-/

open InnerProductSpace Matrix
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma contDiff_inverseHessian {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    ContDiff ℝ 2 (fun x => (coordinateHessian φ x)⁻¹) := by
  have hH := contDiff_coordinateHessian_matrix hφ
  have hd : ContDiff ℝ 2 (fun x => (coordinateHessian φ x).det) :=
    (MatrixCalculus.contDiff_det.of_le (by simp)).comp hH
  have ha : ContDiff ℝ 2 (fun x => (coordinateHessian φ x).adjugate) :=
    (MatrixCalculus.contDiff_adjugate.of_le (by simp)).comp hH
  convert! (hd.inv (fun x => (hpos x).det_pos.ne')).smul ha using 1
  funext x
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

lemma coordinateDerivative_inverseHessian {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (x : Space n) (i a b : Fin n) :
    coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ a b) i x =
      -((coordinateHessian φ x)⁻¹ * hessianDerivative φ x i * (coordinateHessian φ x)⁻¹) a b := by
  unfold coordinateDerivative
  rw [MatrixCalculus.fderiv_matrix_entry
    ((contDiff_inverseHessian hφ hpos).differentiable (by norm_num) x),
    MatrixCalculus.fderiv_matrix_inv_comp_apply
      ((contDiff_coordinateHessian_matrix hφ).differentiable (by norm_num) x)
      (hpos x).det_pos.ne',
    fderiv_coordinateHessian_apply hφ]
  rfl

/-- The first differentiated Monge–Ampère equation, using actual derivatives. -/
theorem trace_inverseHessian_mul_derivative {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x : Space n) (b : Fin n) :
    ((coordinateHessian φ x)⁻¹ * hessianDerivative φ x b).trace =
      (∑ a, coordinateDerivative V a (gradient φ x) * coordinateHessian φ x b a) -
        coordinateDerivative φ b x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hlog := MatrixCalculus.fderiv_logDet_comp_apply_posDef
    ((contDiff_coordinateHessian_matrix hφ).differentiable (by norm_num) x)
    (hpos x) (EuclideanSpace.single b 1)
  rw [fderiv_coordinateHessian_apply hφ] at hlog
  change coordinateDerivative (fun y => Real.log (coordinateHessian φ y).det) b x = _ at hlog
  have hfun : (fun y => Real.log (coordinateHessian φ y).det) =
      fun y => V (gradient φ y) - φ y := by
    funext y
    rw [hMA]
    ring
  rw [hfun, coordinateDerivative_sub
    (f := fun y => V (gradient φ y)) (g := φ)
    ((hV.comp (contDiff_gradient (hφ.of_le (by norm_num) : ContDiff ℝ 3 φ)
      (by norm_num))).differentiable (by norm_num) x)
    (hφ.differentiable (by norm_num) x),
    coordinateDerivative_comp_gradient (hV.differentiable (by norm_num)) hφ2] at hlog
  exact hlog.symm

lemma inverseHessian_divergence_eq_trace {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (x : Space n) (j : Fin n) :
    (∑ i, coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j) i x) =
      -(∑ b, ((coordinateHessian φ x)⁻¹ * hessianDerivative φ x b).trace *
        (coordinateHessian φ x)⁻¹ b j) := by
  simp_rw [coordinateDerivative_inverseHessian hφ hpos, Finset.sum_neg_distrib]
  congr 1
  simp only [Matrix.mul_apply, Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  have ht : hessianDerivative φ x i a b = hessianDerivative φ x b a i := by
    unfold hessianDerivative
    rw [coordinateDerivative_hessian_cycle (hφ.of_le (by norm_num))]
    congr 1
    funext y
    exact (coordinateHessian_symmetric (hφ.of_le (by norm_num)) y).apply a i
  rw [ht]

lemma inverseHessian_contract_drift {φ V : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (x : Space n) (j : Fin n) :
    (∑ b, (∑ a, coordinateDerivative V a (gradient φ x) * coordinateHessian φ x b a) *
      (coordinateHessian φ x)⁻¹ b j) = coordinateDerivative V j (gradient φ x) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinv := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => fun a => M a j)
    (Matrix.mul_nonsing_inv (coordinateHessian φ x) (isUnit_iff_ne_zero.mpr (hpos x).det_pos.ne'))
  have hentry (a : Fin n) : (∑ b, coordinateHessian φ x b a * (coordinateHessian φ x)⁻¹ b j) =
      if a = j then 1 else 0 := by
    have hh := congrFun hinv a
    simp only [Matrix.mul_apply, Matrix.one_apply] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro b _
    rw [(coordinateHessian_symmetric (hφ.of_le (by norm_num)) x).apply a b]
  simp_rw [mul_assoc, ← Finset.mul_sum, hentry]
  simp

/-- The genuine inverse-Hessian divergence has the drift prescribed by V. -/
theorem inverseHessian_weighted_divergence {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x : Space n) (j : Fin n) :
    (∑ i, coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j) i x) -
      (∑ i, coordinateDerivative φ i x * (coordinateHessian φ x)⁻¹ i j) =
      -coordinateDerivative V j (gradient φ x) := by
  rw [inverseHessian_divergence_eq_trace hφ hpos]
  simp_rw [trace_inverseHessian_mul_derivative hφ hV hpos hMA, sub_mul,
    Finset.sum_sub_distrib]
  rw [inverseHessian_contract_drift hφ hpos]
  ring

lemma contDiff_inverseHessian_entry {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (i j : Fin n) :
    ContDiff ℝ 2 (fun x => (coordinateHessian φ x)⁻¹ i j) :=
  contDiff_pi.mp (contDiff_pi.mp (contDiff_inverseHessian hφ hpos) i) j

/-- The concrete operator is the weighted divergence of its actual flux. -/
theorem hessianMetricDiffusion_eq_sum_divergence {φ V g : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hg : ContDiff ℝ 2 g) (x : Space n) :
    hessianMetricDiffusion φ V g x = ∑ j, ∑ i,
      (coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j * coordinateDerivative g j y) i x -
        coordinateDerivative φ i x * ((coordinateHessian φ x)⁻¹ i j * coordinateDerivative g j x)) := by
  have hcolumn (j : Fin n) :
      (∑ i, (coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j *
          coordinateDerivative g j y) i x - coordinateDerivative φ i x *
          ((coordinateHessian φ x)⁻¹ i j * coordinateDerivative g j x))) =
      (∑ i, (coordinateHessian φ x)⁻¹ i j * coordinateHessian g x i j) -
        coordinateDerivative V j (gradient φ x) * coordinateDerivative g j x := by
    have hterm (i : Fin n) :
        coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j * coordinateDerivative g j y) i x -
          coordinateDerivative φ i x * ((coordinateHessian φ x)⁻¹ i j * coordinateDerivative g j x) =
        (coordinateHessian φ x)⁻¹ i j * coordinateHessian g x i j +
          (coordinateDerivative (fun y => (coordinateHessian φ y)⁻¹ i j) i x -
            coordinateDerivative φ i x * (coordinateHessian φ x)⁻¹ i j) * coordinateDerivative g j x := by
      rw [coordinateDerivative_mul
        (f := fun y => (coordinateHessian φ y)⁻¹ i j) (g := coordinateDerivative g j)
        ((contDiff_inverseHessian_entry hφ hpos i j).differentiable (by norm_num) x)
        ((contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable (by norm_num) x)]
      change _ - _ = (coordinateHessian φ x)⁻¹ i j *
        coordinateDerivative (coordinateDerivative g j) i x + _
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
    rw [inverseHessian_weighted_divergence hφ hV hpos hMA]
    ring
  simp_rw [hcolumn, Finset.sum_sub_distrib]
  unfold hessianMetricDiffusion
  congr 1
  rw [Finset.sum_comm]

end KLS
end

#print axioms KLS.contDiff_inverseHessian
#print axioms KLS.trace_inverseHessian_mul_derivative
#print axioms KLS.inverseHessian_weighted_divergence
#print axioms KLS.hessianMetricDiffusion_eq_sum_divergence
