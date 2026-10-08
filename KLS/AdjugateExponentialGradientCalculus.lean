import KLS.WeakMomentLocallyLipschitzAdjugateTests

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The cofactor contraction uses the actual symmetric matrix and its adjugate. -/
theorem adjugate_column_gradient_contraction
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (b : Fin n → ℝ) (j : Fin n) :
    (∑ i, H.adjugate i j * (∑ a, b a * H i a)) = H.det * b j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (a : Fin n) : (∑ i, H.adjugate i j * (b a * H i a)) =
      b a * (H*H.adjugate) a j := by
    rw [Matrix.mul_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hH.apply i a]
    ring
  simp_rw [he]
  rw [Matrix.mul_adjugate]
  simp [Matrix.one_apply,mul_comm]

/-- The chain rule through the actual gradient only requires a derivative at
 the point, with no continuous Hessian hypothesis. -/
theorem coordinateDerivative_exp_neg_comp_gradient
    {u V : Space n → ℝ} {x : Space n}
    (hV : DifferentiableAt ℝ V (gradient u x))
    (hg : DifferentiableAt ℝ (gradient u) x) (i : Fin n) :
    coordinateDerivative (fun y => Real.exp (-V (gradient u y))) i x =
      -Real.exp (-V (gradient u x)) *
        (∑ a, coordinateDerivative V a (gradient u x)*coordinateHessian u x i a) := by
  change fderiv ℝ (fun y => Real.exp (-V (gradient u y))) x (EuclideanSpace.single i 1) = _
  rw [fderiv_exp_neg_apply (show DifferentiableAt ℝ (fun y => V (gradient u y)) x from hV.comp x hg)]
  change -(Real.exp (-V (gradient u x))*coordinateDerivative (fun y => V (gradient u y)) i x) = _
  rw [coordinateDerivative_comp hV hg]
  have he (a : Fin n) : (fun y => gradient u y a) = coordinateDerivative u a := by
    funext y
    exact (coordinateDerivative_eq_gradient u a y).symm
  simp_rw [he]
  simp only [coordinateHessian,neg_mul]

/-- Multiplication by the target exponential is an admissible compact locally
 Lipschitz test for the actual C1,1 gradient. -/
theorem locallyLipschitz_mul_exp_neg_comp_gradient
    {u V ψ : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) (hψ : LocallyLipschitz ψ) :
    LocallyLipschitz (fun x => ψ x*Real.exp (-V (gradient u x))) := by
  have he := hV.neg.exp.locallyLipschitz.comp hG.locallyLipschitz
  have hm : LocallyLipschitz (fun p : ℝ×ℝ => p.1*p.2) :=
    (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.1*p.2)).locallyLipschitz
  exact hm.comp (hψ.prodMk he)

/-- The actual Monge-Ampere equation converts the weighted adjugate to the
 density times the actual inverse Hessian. -/
theorem exp_neg_target_mul_adjugate_eq_exp_neg_source_mul_inverse
    {u V : Space n → ℝ} {x : Space n} (hp : (coordinateHessian u x).PosDef)
    (hMA : (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (i j : Fin n) :
    Real.exp (-V (gradient u x)) * (coordinateHessian u x).adjugate i j =
      Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j := by
  rw [← det_smul_nonsing_inv_eq_adjugate hp.det_pos.ne']
  change Real.exp (-V (gradient u x))*((coordinateHessian u x).det * _) = _
  rw [hMA,← mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- The exact pointwise product identity needed by weak inverse-Hessian
 divergence, valid at each actual gradient derivative point satisfying MA. -/
theorem adjugate_exp_neg_gradient_test_identity
    {u V ψ : Space n → ℝ} {x : Space n}
    (hV : DifferentiableAt ℝ V (gradient u x)) (hψ : DifferentiableAt ℝ ψ x)
    (hg : DifferentiableAt ℝ (gradient u) x) (hp : (coordinateHessian u x).PosDef)
    (hMA : (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x))) (j : Fin n) :
    (∑ i, (coordinateHessian u x).adjugate i j *
      coordinateDerivative (fun y => ψ y*Real.exp (-V (gradient u y))) i x) =
    (∑ i, Real.exp (-V (gradient u x)) * (coordinateHessian u x).adjugate i j *
      coordinateDerivative ψ i x) -
      Real.exp (-u x)*coordinateDerivative V j (gradient u x)*ψ x := by
  have he : DifferentiableAt ℝ (fun y => Real.exp (-V (gradient u y))) x := (hV.comp x hg).neg.exp
  simp_rw [coordinateDerivative_mul hψ he,coordinateDerivative_exp_neg_comp_gradient hV hg]
  have hsplit : (∑ i, (coordinateHessian u x).adjugate i j *
      (coordinateDerivative ψ i x*Real.exp (-V (gradient u x)) +
       ψ x*(-Real.exp (-V (gradient u x)) *
         (∑ a, coordinateDerivative V a (gradient u x)*coordinateHessian u x i a)))) =
      (∑ i, Real.exp (-V (gradient u x)) * (coordinateHessian u x).adjugate i j *
        coordinateDerivative ψ i x) -
      Real.exp (-V (gradient u x))*ψ x *
        (∑ i, (coordinateHessian u x).adjugate i j *
          (∑ a, coordinateDerivative V a (gradient u x)*coordinateHessian u x i a)) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit,adjugate_column_gradient_contraction _ hp.isHermitian.isSymm,hMA]
  have hexp : Real.exp (-V (gradient u x))*Real.exp (-u x + V (gradient u x)) = Real.exp (-u x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  congr 1
  calc
    _ = (Real.exp (-V (gradient u x))*Real.exp (-u x + V (gradient u x))) *
        coordinateDerivative V j (gradient u x)*ψ x := by ring
    _ = _ := by rw [hexp]

end KLS
end
