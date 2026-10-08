import KLS.WeakMomentLipschitzInverseTests

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual second-order expression with measurable matrix coefficients
 and a prescribed drift. All derivatives here are actual total derivatives. -/
def weakEllipticExpression (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → Space n → ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  (∑ i, ∑ j, A x i j*coordinateHessian f x i j) -
    ∑ j, b j x*coordinateDerivative f j x

/-- The pointwise cancellation behind compact self-adjoint transfer requires
 symmetry of the coefficient matrix, not derivatives of that matrix. -/
theorem weak_elliptic_green_algebra
    (A F E : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (b df de : Fin n → ℝ) (f e : ℝ) :
    (∑ j, ∑ i, A i j*((de i*df j+e*F i j)-(df i*de j+f*E i j))) -
        (∑ j, b j*(e*df j-f*de j)) =
      e*((∑ i, ∑ j, A i j*F i j)-(∑ j, b j*df j)) -
        f*((∑ i, ∑ j, A i j*E i j)-(∑ j, b j*de j)) := by
  have hc : (∑ j, ∑ i, A i j*(de i*df j)) = ∑ j, ∑ i, A i j*(df i*de j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hA.apply j i]
    ring
  have hF : (∑ j, ∑ i, A i j*(e*F i j)) = e*(∑ i, ∑ j, A i j*F i j) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hE : (∑ j, ∑ i, A i j*(f*E i j)) = f*(∑ i, ∑ j, A i j*E i j) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbe : (∑ j, b j*(e*df j)) = e*(∑ j, b j*df j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbf : (∑ j, b j*(f*de j)) = f*(∑ j, b j*de j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hc,hF,hE,hbe,hbf]
  ring

/-- Multiplication of scalar locally Lipschitz functions is locally Lipschitz. -/
theorem locallyLipschitz_mul_real {f g : Space n → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x*g x) :=
  (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.1*p.2)).locallyLipschitz.comp (hf.prodMk hg)

/-- Subtraction of scalar locally Lipschitz functions is locally Lipschitz. -/
theorem locallyLipschitz_sub_real {f g : Space n → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x-g x) :=
  (contDiff_fst.sub contDiff_snd : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.1-p.2)).locallyLipschitz.comp (hf.prodMk hg)

end KLS
end
