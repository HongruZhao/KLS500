import KLS.TensorMetricSmooth
import KLS.TensorCoordinateExpansion
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Finite coordinate tensors and their real homogeneous polynomials. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def tensorPolynomial (T : (Fin r → Fin n) → ℝ) (x : Space n) : ℝ :=
  ∑ a, T a * ∏ s, x (a s)

theorem tensorPolynomial_add (T U : (Fin r → Fin n) → ℝ) (x : Space n) :
    tensorPolynomial (T+U) x = tensorPolynomial T x + tensorPolynomial U x := by
  simp [tensorPolynomial, add_mul, Finset.sum_add_distrib]

theorem tensorPolynomial_smul (c : ℝ) (T : (Fin r → Fin n) → ℝ) (x : Space n) :
    tensorPolynomial (c • T) x = c * tensorPolynomial T x := by
  simp [tensorPolynomial, Finset.mul_sum, mul_assoc]

theorem tensorPolynomial_sum {ι : Type*} [Fintype ι]
    (T : ι → (Fin r → Fin n) → ℝ) (x : Space n) :
    tensorPolynomial (∑ i, T i) x = ∑ i, tensorPolynomial (T i) x := by
  simp only [tensorPolynomial, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem tensorPolynomial_homogeneous (T : (Fin r → Fin n) → ℝ) (c : ℝ) (x : Space n) :
    tensorPolynomial T (c • x) = c^r * tensorPolynomial T x := by
  simp only [tensorPolynomial, PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem contDiff_tensorPolynomial (T : (Fin r → Fin n) → ℝ) :
    ContDiff ℝ ⊤ (tensorPolynomial T) := by
  unfold tensorPolynomial
  apply ContDiff.sum
  intro a _
  exact contDiff_const.mul (contDiff_prod fun s _ => (EuclideanSpace.proj (𝕜 := ℝ) (a s)).contDiff)

theorem fderiv_tensorPolynomial (T : (Fin r → Fin n) → ℝ) (x v : Space n) :
    fderiv ℝ (tensorPolynomial T) x v =
      ∑ a, T a * ∑ s, (∏ j ∈ Finset.univ.erase s, x (a j)) * v (a s) := by
  have hp (a : Fin r → Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space n => ∏ s, y (a s)) :=
    contDiff_prod fun s _ => (EuclideanSpace.proj (𝕜 := ℝ) (a s)).contDiff
  have he (i : Fin n) : fderiv ℝ (fun y : Space n => y i) x v = v i := by
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L v)
      (EuclideanSpace.proj (𝕜 := ℝ) i).fderiv
  unfold tensorPolynomial
  rw [fderiv_fun_sum]
  · simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [fderiv_const_mul]
    · rw [fderiv_finsetProd]
      · simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
          he]
      · intro s _
        exact (EuclideanSpace.proj (𝕜 := ℝ) (a s)).differentiableAt
    · exact ((hp a).differentiable (by simp)).differentiableAt
  · intro a _
    exact ((contDiff_const.mul (hp a)).differentiable (by simp)).differentiableAt

end KLS.TensorEnergy
end
