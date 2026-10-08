import KLS.WeightedDiffusionCommutator

/-!
# Integrated Bochner identity for the actual weighted diffusion

For the actual measure `exp(-φ) dx`, C² potential, C³ test, and explicit L¹
requirements, the squared diffusion integrates to the Hessian square plus
the Hessian-potential gradient quadratic form. No Poincaré or Brascamp--Lieb
bound is assumed. The integration and derivative-commutation steps are proved.
-/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Squared Hilbert--Schmidt norm of the actual coordinate Hessian; all ordered pairs count. -/
def hessianSquare (g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (coordinateHessian g x i j) ^ 2

/-- The Hessian of the potential applied twice to the test gradient. -/
def hessianGradientForm (φ g : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x

/-- Explicit integration domain for the integrated Bochner calculation. -/
structure BochnerIntegrability (φ g : Space n → ℝ) : Prop where
  diffusion : DiffusionIntegrability φ (weightedDiffusion φ g) g
  derivatives : ∀ i, DiffusionIntegrability φ (coordinateDerivative g i) (coordinateDerivative g i)
  curvature : ∀ i j, Integrable
    (fun x => coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x)
    (potentialMeasure φ)

lemma norm_gradient_coordinateDerivative_sq (g : Space n → ℝ) (i : Fin n) (x : Space n) :
    ‖gradient (coordinateDerivative g i) x‖ ^ 2 =
      ∑ j : Fin n, (coordinateHessian g x j i) ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, ← coordinateDerivative_eq_gradient]
  rfl

lemma sum_norm_gradient_coordinateDerivative_sq (g : Space n → ℝ) (x : Space n) :
    (∑ i : Fin n, ‖gradient (coordinateDerivative g i) x‖ ^ 2) = hessianSquare g x := by
  simp_rw [norm_gradient_coordinateDerivative_sq]
  exact Finset.sum_comm

lemma BochnerIntegrability.integrable_gradient_coordinateDerivative_sq {φ g : Space n → ℝ}
    (h : BochnerIntegrability φ g) (i : Fin n) :
    Integrable (fun x => ‖gradient (coordinateDerivative g i) x‖ ^ 2) (potentialMeasure φ) := by
  simpa only [real_inner_self_eq_norm_sq] using
    (h.derivatives i).integrable_inner_gradient

lemma BochnerIntegrability.integrable_curvature_row {φ g : Space n → ℝ}
    (h : BochnerIntegrability φ g) (i : Fin n) :
    Integrable (fun x => ∑ j : Fin n,
      coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x)
      (potentialMeasure φ) :=
  integrable_finsetSum Finset.univ (fun j _ => h.curvature i j)

lemma BochnerIntegrability.integrable_diffusion_sq {φ g : Space n → ℝ}
    (h : BochnerIntegrability φ g) :
    Integrable (fun x => (weightedDiffusion φ g x) ^ 2) (potentialMeasure φ) := by
  simpa only [pow_two] using h.diffusion.integrable_mul_diffusion

lemma BochnerIntegrability.integrable_hessianSquare {φ g : Space n → ℝ}
    (h : BochnerIntegrability φ g) : Integrable (hessianSquare g) (potentialMeasure φ) := by
  have hi := integrable_finsetSum Finset.univ
    (fun i _ => h.integrable_gradient_coordinateDerivative_sq i)
  simpa only [sum_norm_gradient_coordinateDerivative_sq] using hi

lemma BochnerIntegrability.integrable_hessianGradientForm {φ g : Space n → ℝ}
    (h : BochnerIntegrability φ g) : Integrable (hessianGradientForm φ g) (potentialMeasure φ) :=
  integrable_finsetSum Finset.univ (fun i _ => h.integrable_curvature_row i)

/-- A single coordinate's integrated commutator calculation. -/
theorem integrated_bochner_coordinate {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g)
    (h : BochnerIntegrability φ g) (i : Fin n) :
    -(∫ x, coordinateDerivative (weightedDiffusion φ g) i x * coordinateDerivative g i x
      ∂potentialMeasure φ) =
      (∫ x, ‖gradient (coordinateDerivative g i) x‖ ^ 2 ∂potentialMeasure φ) +
      ∫ x, ∑ j : Fin n,
        coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x
        ∂potentialMeasure φ := by
  have hgi : ContDiff ℝ 2 (coordinateDerivative g i) :=
    contDiff_coordinateDerivative hg (by norm_num) i
  have he := integral_mul_weightedDiffusion_self (hφ.differentiable (by norm_num))
    (hgi.differentiable (by norm_num))
    (fun j => (contDiff_coordinateDerivative hgi (m := 1) (by norm_num) j).differentiable
      (by norm_num)) (h.derivatives i)
  have heq : (fun x => coordinateDerivative (weightedDiffusion φ g) i x * coordinateDerivative g i x) =
      (fun x => coordinateDerivative g i x * weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j : Fin n,
          coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x) := by
    funext x
    rw [coordinateDerivative_weightedDiffusion hφ hg, sub_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [heq, integral_sub (h.derivatives i).integrable_mul_diffusion
    (h.integrable_curvature_row i), he]
  ring

/-- Integrated Bochner identity, with genuine diffusion, Hessian and density. -/
theorem integral_weightedDiffusion_sq {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (h : BochnerIntegrability φ g) :
    (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) =
      ∫ x, hessianSquare g x + hessianGradientForm φ g x ∂potentialMeasure φ := by
  have hdi : Differentiable ℝ (weightedDiffusion φ g) :=
    (contDiff_weightedDiffusion hφ hg).differentiable (by norm_num)
  have hb := integral_mul_weightedDiffusion (hφ.differentiable (by norm_num)) hdi
    (fun i => (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).differentiable
      (by norm_num)) h.diffusion
  simp only [← pow_two] at hb
  rw [hb]
  simp_rw [← sum_coordinateDerivative_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => h.diffusion.deriv_mul_deriv i),
    ← Finset.sum_neg_distrib]
  simp_rw [integrated_bochner_coordinate hφ hg h]
  rw [Finset.sum_add_distrib,
    ← integral_finsetSum Finset.univ (fun i _ => h.integrable_gradient_coordinateDerivative_sq i),
    ← integral_finsetSum Finset.univ (fun i _ => h.integrable_curvature_row i)]
  simp_rw [sum_norm_gradient_coordinateDerivative_sq]
  exact (integral_add h.integrable_hessianSquare h.integrable_hessianGradientForm).symm

/-- Equivalent split form of the integrated Bochner identity. -/
theorem integral_weightedDiffusion_sq_eq_sum {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (h : BochnerIntegrability φ g) :
    (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) =
      (∫ x, hessianSquare g x ∂potentialMeasure φ) +
        ∫ x, hessianGradientForm φ g x ∂potentialMeasure φ := by
  rw [integral_weightedDiffusion_sq hφ hg h,
    integral_add h.integrable_hessianSquare h.integrable_hessianGradientForm]

end KLS
end

#print axioms KLS.integrated_bochner_coordinate
#print axioms KLS.integral_weightedDiffusion_sq
#print axioms KLS.integral_weightedDiffusion_sq_eq_sum
