import KLS.DirectionalWordAlgebra
import KLS.WeightedTiltFirstDerivative

/-! The full mixed Taylor identity for the genuine weighted diffusion tilt.
All tilted observables are proved smooth from the actual weighted L2 domain. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual tilted negative diffusion has exactly the omitted-direction
mixed derivative sum. No diagonal-only identity or derivative premise occurs. -/
theorem weightedDiffusion_exponentialTilt_mixed_derivative
    {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (d : ℕ) (m : Fin (d + 1) → Space n) :
    iteratedFDeriv ℝ (d + 1)
      (fun z => ∫ x, -weightedDiffusion φ f x
        ∂exponentialTilt (potentialMeasure φ) z) 0 m =
      ∑ k : Fin (d + 1), iteratedFDeriv ℝ d
        (fun z => ∫ x, inner ℝ (m k) (gradient f x)
          ∂exponentialTilt (potentialMeasure φ) z) 0
        (fun j => m (k.succAbove j)) := by
  let G : Fin n → Space n → ℝ := fun i z =>
    ∫ x, gradient f x i ∂exponentialTilt (potentialMeasure φ) z
  have hG (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (G i) :=
    contDiff_exponentialTilt_gradient_coordinate hφ hκ hlower
      (hf.of_le (by norm_num)) hF i
  have he : (fun z => ∫ x, -weightedDiffusion φ f x
      ∂exponentialTilt (potentialMeasure φ) z) = fun z => ∑ i, z i * G i z := by
    funext z
    rw [weightedDiffusion_exponentialTilt_identity hφ hκ hlower hf hL hF]
    rw [real_inner_comm, inner_eq_coordinate_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).integral_comp_comm
      (integrable_gradient_exponentialTilt_of_L2 hφ hκ hlower
        (hf.of_le (by norm_num)) hF z)).symm
  have hi (v : Space n) : (fun z => ∫ x, inner ℝ v (gradient f x)
      ∂exponentialTilt (potentialMeasure φ) z) = fun z => ∑ i, v i * G i z := by
    funext z
    change (∫ x, (innerSL ℝ v) (gradient f x)
      ∂exponentialTilt (potentialMeasure φ) z) = _
    rw [(innerSL ℝ v).integral_comp_comm
      (integrable_gradient_exponentialTilt_of_L2 hφ hκ hlower
        (hf.of_le (by norm_num)) hF z)]
    rw [innerSL_apply_apply, real_inner_comm, inner_eq_coordinate_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).integral_comp_comm
      (integrable_gradient_exponentialTilt_of_L2 hφ hκ hlower
        (hf.of_le (by norm_num)) hF z)).symm
  have hprod (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space n => z i * G i z) :=
    (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.mul (hG i)
  rw [he, ← directionalWordDerivative_ofFn (ContDiff.sum fun i _ => hprod i),
    directionalWordDerivative_sum _ (fun i _ => hprod i)]
  simp_rw [directionalWordDerivative_ofFn (hprod _)]
  change (∑ i, iteratedFDeriv ℝ (d + 1)
    (fun z => (EuclideanSpace.proj i : Space n →L[ℝ] ℝ) z * G i z) 0 m) = _
  simp_rw [iteratedFDeriv_linear_mul_zero (hG _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [hi, ← directionalWordDerivative_ofFn (by
    exact ContDiff.sum fun i _ => contDiff_const.mul (hG i)),
    directionalWordDerivative_sum _ (fun i _ => contDiff_const.mul (hG i))]
  simp_rw [directionalWordDerivative_const_mul (hG _),
    directionalWordDerivative_ofFn (hG _)]
  rfl

end KLS
end

#print axioms KLS.weightedDiffusion_exponentialTilt_mixed_derivative
