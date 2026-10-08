import KLS.WeightedMollification

/-!
# A cutoff gradient estimate for the mollified divergence equation

Actual classical solutions of Δh = -div F obey a local energy estimate. The
compact cutoff discharges every boundary and integrability condition. This is
the estimate needed before taking weak limits of mollified gradients.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma integral_mul_coordinateDerivative_of_hasCompactSupport_left {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) (i : Fin n) :
    (∫ x, f x * coordinateDerivative g i x) =
      -(∫ x, coordinateDerivative f i x * g x) := by
  have hdf := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i).mul_right)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport hc.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)

/-- A C¹ divergence-free field annihilates the gradient of every compact C¹ scalar test. -/
theorem integral_gradient_mul_eq_zero_of_divergence_zero {f : Space n → ℝ}
    {G : Fin n → Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hdiv : ∀ x, ∑ i, coordinateDerivative (G i) i x = 0) :
    (∫ x, ∑ i, coordinateDerivative f i x * G i x) = 0 := by
  have hleft (i : Fin n) : Integrable (fun x => f x * coordinateDerivative (G i) i x) volume :=
    (hf.continuous.mul (contDiff_coordinateDerivative (hG i) (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hright (i : Fin n) : Integrable (fun x => coordinateDerivative f i x * G i x) volume :=
    ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.mul (hG i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_mul_coordinateDerivative_of_hasCompactSupport_left hf (hG i) hc i)
  rw [← integral_finsetSum _ (fun i _ => hleft i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hright i)] at hsum
  have hz : (∫ x, ∑ i, f x * coordinateDerivative (G i) i x) = 0 := by
    simp_rw [← Finset.mul_sum, hdiv, mul_zero, integral_zero]
  rw [hz] at hsum
  exact neg_eq_zero.mp hsum.symm

/-- Forced Caccioppoli estimate in actual coordinate derivatives.
The constants are numerical consequences of three elementary square inequalities. -/
theorem forced_caccioppoli_coordinate {χ h : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 2 h) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hc : HasCompactSupport χ)
    (heq : ∀ x, coordinateLaplacian h x = -(∑ i, coordinateDerivative (F i) i x)) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      10 * (∫ x, ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) +
        4 * (∫ x, ∑ i, χ x ^ 2 * F i x ^ 2) := by
  let f : Space n → ℝ := fun x => χ x * χ x * h x
  have hf : ContDiff ℝ 1 f := (hχ.mul hχ).mul (hh.of_le (by norm_num))
  have hfc : HasCompactSupport f := hc.mul_right.mul_right
  have hG (i : Fin n) : ContDiff ℝ 1 (fun x => coordinateDerivative h i x + F i x) :=
    (contDiff_coordinateDerivative hh (m := 1) (by norm_num) i).add (hF i)
  have hdiv (x : Space n) : ∑ i, coordinateDerivative
      (fun y => coordinateDerivative h i y + F i y) i x = 0 := by
    have hcoord (i : Fin n) : coordinateDerivative
        (fun y => coordinateDerivative h i y + F i y) i x =
          coordinateHessian h x i i + coordinateDerivative (F i) i x :=
      coordinateDerivative_add
        ((contDiff_coordinateDerivative hh (m := 1) (by norm_num) i).differentiable
          (by norm_num) x) ((hF i).differentiable (by norm_num) x) i
    rw [Finset.sum_congr rfl (fun i _ => hcoord i), Finset.sum_add_distrib]
    change coordinateLaplacian h x + ∑ i, coordinateDerivative (F i) i x = 0
    rw [heq]
    ring
  have hzero := integral_gradient_mul_eq_zero_of_divergence_zero hf hfc hG hdiv
  have hdf (i : Fin n) (x : Space n) : coordinateDerivative f i x =
      2 * χ x * h x * coordinateDerivative χ i x + χ x ^ 2 * coordinateDerivative h i x := by
    dsimp only [f]
    have hdχχ : DifferentiableAt ℝ (fun y => χ y * χ y) x := by
      exact ((hχ.mul hχ).differentiable (by norm_num)) x
    rw [coordinateDerivative_mul hdχχ (hh.differentiable (by norm_num) x),
      coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hχ.differentiable (by norm_num) x)]
    ring
  have hdcχ (i : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hdch (i : Fin n) := (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous
  have hE : Integrable (fun x => ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) volume :=
    integrable_finsetSum _ (fun i _ =>
      ((hχ.continuous.pow 2).mul ((hdch i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right))
  have hA : Integrable (fun x => ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) volume :=
    integrable_finsetSum _ (fun i _ =>
      ((hh.continuous.pow 2).mul ((hdcχ i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using
          (hasCompactSupport_coordinateDerivative hc i).mul_right.mul_left))
  have hB : Integrable (fun x => ∑ i, χ x ^ 2 * F i x ^ 2) volume :=
    integrable_finsetSum _ (fun i _ =>
      ((hχ.continuous.pow 2).mul ((hF i).continuous.pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right))
  have hD : Integrable (fun x => ∑ i, coordinateDerivative f i x *
      (coordinateDerivative h i x + F i x)) volume :=
    integrable_finsetSum _ (fun i _ =>
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.mul (hG i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hfc i).mul_right)
  have hsquare (a b c : ℝ) : a ^ 2 ≤ 10 * b ^ 2 + 4 * c ^ 2 +
      2 * (a ^ 2 + 2 * a * b + a * c + 2 * b * c) := by
    nlinarith [sq_nonneg (a / 2 + 2 * b), sq_nonneg (a / 2 + c), sq_nonneg (b + c)]
  have hp (x : Space n) : (∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      10 * (∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) +
        4 * (∑ i, χ x ^ 2 * F i x ^ 2) +
          2 * (∑ i, coordinateDerivative f i x * (coordinateDerivative h i x + F i x)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hdf]
    nlinarith [hsquare (χ x * coordinateDerivative h i x)
      (h x * coordinateDerivative χ i x) (χ x * F i x)]
  have hm := integral_mono hE (((hA.const_mul 10).add (hB.const_mul 4)).add (hD.const_mul 2)) hp
  have hsplit := integral_add ((hA.const_mul 10).add (hB.const_mul 4)) (hD.const_mul 2)
  have hsplit' := integral_add (hA.const_mul 10) (hB.const_mul 4)
  simp only [Pi.add_apply] at hm hsplit hsplit'
  rw [hsplit, hsplit', integral_const_mul, integral_const_mul, integral_const_mul,
    hzero, mul_zero, add_zero] at hm

  exact hm

end KLS
end

#print axioms KLS.integral_mul_coordinateDerivative_of_hasCompactSupport_left
#print axioms KLS.integral_gradient_mul_eq_zero_of_divergence_zero
#print axioms KLS.forced_caccioppoli_coordinate
