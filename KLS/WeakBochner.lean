import KLS.WeakDiffusionCommutator
import KLS.LocalWeakFiniteProduct

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Integrated Bochner for the actual C1,1 potential. Only the compact
test is C3; the potential Hessian is its almost-everywhere actual derivative. -/
theorem integral_weightedDiffusion_sq_C11
    {φ g : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hG : LocallyLipschitz (gradient φ)) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    Integrable (hessianSquare g) (potentialMeasure φ) ∧
    Integrable (hessianGradientForm φ g) (potentialMeasure φ) ∧
    (∫ x, weightedDiffusion φ g x ^ 2 ∂potentialMeasure φ) =
      (∫ x, hessianSquare g x ∂potentialMeasure φ) +
        ∫ x, hessianGradientForm φ g x ∂potentialMeasure φ := by
  let C : Fin n → Space n → ℝ := fun i x =>
    weightedDiffusion φ (coordinateDerivative g i) x -
      ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x
  have hgi (i : Fin n) : ContDiff ℝ 2 (coordinateDerivative g i) :=
    contDiff_coordinateDerivative hg (by norm_num) i
  have hCw (i : Fin n) := (weak_weightedDiffusion_commutator hG hg i).2.1
  have hCl (i : Fin n) : LocallyIntegrable (C i) volume :=
    locallyIntegrable_of_memLp_two_on_compacts (memLp_two_on_compacts_of_top
      (weak_weightedDiffusion_commutator hG hg i).2.2)
  have hp := raw_weak_gradient_pairing_eq_neg_diffusion hφ
    (locallyLipschitz_weightedDiffusion hG hg).continuous.locallyIntegrable hCl hCw
    (hg.of_le (by norm_num)) hc
  have hH (i j : Fin n) : LocallyIntegrable (fun x => coordinateHessian φ x i j) volume :=
    locallyIntegrable_coordinateDerivative_of_locallyLipschitz
      (locallyLipschitz_coordinateDerivative_of_gradient hG j) i
  have hcurv (i j : Fin n) : Integrable (fun x =>
      coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x)
      (potentialMeasure φ) := by
    have ht : Integrable (fun x => coordinateHessian φ x i j *
        (coordinateDerivative g i x * coordinateDerivative g j x)) (potentialMeasure φ) :=
      integrable_raw_mul_compact_potential hφ.continuous (hH i j)
        ((hgi i).continuous.mul (hgi j).continuous)
        (hasCompactSupport_coordinateDerivative hc i).mul_right
    simpa only [mul_assoc] using ht
  have hrow (i : Fin n) : Integrable (fun x => ∑ j,
      coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x)
      (potentialMeasure φ) := integrable_finsetSum _ (fun j _ => hcurv i j)
  have hcurvint : Integrable (hessianGradientForm φ g) (potentialMeasure φ) :=
    integrable_finsetSum _ (fun i _ => hrow i)
  have hdom (i : Fin n) := diffusionIntegrability_of_hasCompactSupport hφ
    ((hgi i).of_le (by norm_num)) (hgi i) (hasCompactSupport_coordinateDerivative hc i)
  have hnorm (i : Fin n) : Integrable (fun x => ‖gradient (coordinateDerivative g i) x‖ ^ 2)
      (potentialMeasure φ) := by
    simpa only [real_inner_self_eq_norm_sq] using (hdom i).integrable_inner_gradient
  have hsquare : Integrable (hessianSquare g) (potentialMeasure φ) := by
    have hh := integrable_finsetSum Finset.univ (fun i _ => hnorm i)
    simpa only [sum_norm_gradient_coordinateDerivative_sq] using hh
  have hcoord (i : Fin n) :
      -(∫ x, C i x * coordinateDerivative g i x ∂potentialMeasure φ) =
        (∫ x, ‖gradient (coordinateDerivative g i) x‖ ^ 2 ∂potentialMeasure φ) +
          ∫ x, ∑ j, coordinateHessian φ x i j * coordinateDerivative g i x *
            coordinateDerivative g j x ∂potentialMeasure φ := by
    have he := integral_mul_weightedDiffusion_of_hasCompactSupport hφ
      ((hgi i).of_le (by norm_num)) (hgi i) (hasCompactSupport_coordinateDerivative hc i)
    simp only [real_inner_self_eq_norm_sq] at he
    have hfun : (fun x => C i x * coordinateDerivative g i x) =
        (fun x => coordinateDerivative g i x * weightedDiffusion φ (coordinateDerivative g i) x -
          ∑ j, coordinateHessian φ x i j * coordinateDerivative g i x * coordinateDerivative g j x) := by
      funext x
      dsimp only [C]
      rw [sub_mul, Finset.sum_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun, integral_sub (hdom i).integrable_mul_diffusion (hrow i), he]
    ring
  refine ⟨hsquare, hcurvint, ?_⟩
  calc
    _ = -(∑ i, ∫ x, C i x * coordinateDerivative g i x ∂potentialMeasure φ) := by
      have hh := hp.2.2
      simp only [← pow_two] at hh
      linarith
    _ = ∑ i, -(∫ x, C i x * coordinateDerivative g i x ∂potentialMeasure φ) :=
      by rw [Finset.sum_neg_distrib]
    _ = ∑ i, ((∫ x, ‖gradient (coordinateDerivative g i) x‖ ^ 2 ∂potentialMeasure φ) +
        ∫ x, ∑ j, coordinateHessian φ x i j * coordinateDerivative g i x *
          coordinateDerivative g j x ∂potentialMeasure φ) :=
      Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = _ := by
      rw [Finset.sum_add_distrib,
        ← integral_finsetSum _ (fun i _ => hnorm i), ← integral_finsetSum _ (fun i _ => hrow i)]
      simp only [sum_norm_gradient_coordinateDerivative_sq, hessianGradientForm]

theorem integral_hessianGradientForm_le_diffusion_sq_C11
    {φ g : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hG : LocallyLipschitz (gradient φ)) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, hessianGradientForm φ g x ∂potentialMeasure φ) ≤
      ∫ x, weightedDiffusion φ g x ^ 2 ∂potentialMeasure φ := by
  rw [(integral_weightedDiffusion_sq_C11 hφ hG hg hc).2.2]
  exact le_add_of_nonneg_left (integral_nonneg (hessianSquare_nonneg g))

end KLS
end
