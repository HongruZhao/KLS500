import KLS.WeightedTaylorLowOrder

/-! The actual mean loss is the squared order-one Taylor tensor of the actual diffusion. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

theorem weightedIterationMeanLoss_eq_diffusion_taylor (k : ℕ) :
    weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U k =
      ∑ ji : Fin n × WeightedIterationIndex n ι k,
        exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ (F k ji.2)) 1 (fun _ => ji.1) ^ 2 := by
  unfold weightedIterationMeanLoss
  apply Finset.sum_congr rfl
  rintro ⟨j, i⟩ _
  rw [weightedFamilyGradient_apply]
  have hd := weightedH1_coordinateDerivative_of_representative (hφ.of_le (by simp))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i)
    ((hF k i).of_le (by simp)) (hV k i) j
  have hi : (∫ x, coordinateDerivative (F k i) j x ∂potentialMeasure φ) =
      ∫ x, weightedH1Derivative φ j
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) x ∂potentialMeasure φ :=
    integral_congr_ae ((withDensity_absolutelyContinuous _ _).ae_eq hd)
  rw [← hi]
  congr 1
  exact (weightedDiffusion_exponentialTiltCoordinateTaylor_one (hφ.of_le (by simp)) hκ hlower
    ((hF k i).of_le (by simp)) (hL k i)
    (weightedH1_integrable_gradient_norm_sq_of_representative (hφ.of_le (by simp))
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i)
      ((hF k i).of_le (by simp)) (hV k i)) (fun _ => j)).symm

/-- Every successive mean loss is exactly the scale squared times the genuine
order-one Taylor tensor of the preceding centered graph gradient. -/
theorem weightedIterationMeanLoss_succ_eq_scale_taylor (k : ℕ) :
    weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U (k + 1) =
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 *
      ‖weightedL2TaylorTensor φ 1 (weightedFamilyCenteredGradient φ
        (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))‖ ^ 2 := by
  rw [weightedIterationMeanLoss_eq_diffusion_taylor hφ hκ hlower U F hF hV hL (k + 1),
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_prod_type]
  change (∑ j : Fin n, ∑ i : Fin n × WeightedIterationIndex n ι k,
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ (F (k + 1) i)) 1 (fun _ => j) ^ 2) = _
  simp_rw [weightedIteration_diffusion_taylor_recursion hφ hκ hlower U F hF hV,
    mul_pow]
  simp_rw [← Finset.mul_sum]
  congr 1
  have he := (Equiv.funUnique (Fin 1) (Fin n)).sum_comp
    (fun j => ∑ i : WeightedIterationIndex n ι (k + 1),
      exponentialTiltCoordinateTaylor φ (weightedCenteredGradientCoordinate φ (F k i.2) i.1) 1
        (fun _ => j) ^ 2)
  calc
    _ = ∑ a : Fin 1 → Fin n, ∑ i : Fin n × WeightedIterationIndex n ι k,
        exponentialTiltCoordinateTaylor φ (weightedCenteredGradientCoordinate φ (F k i.2) i.1) 1
          (fun _ => a 0) ^ 2 := he.symm
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  have hca := weightedFamilyCenteredGradient_ae_of_representative (hφ.of_le (by simp))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)
    (F k) (fun i => (hF k i).of_le (by simp)) (hV k) i
  rw [weightedL2TaylorTensor_apply, exponentialTiltCoordinateTaylor_congr_ae hca]
  congr 2
  funext z
  exact congrArg a (Subsingleton.elim (0 : Fin 1) z)

end KLS
end
#print axioms KLS.weightedIterationMeanLoss_eq_diffusion_taylor
#print axioms KLS.weightedIterationMeanLoss_succ_eq_scale_taylor
