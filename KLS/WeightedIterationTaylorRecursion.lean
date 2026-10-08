import KLS.WeightedCenteredGradientTaylor
import KLS.WeightedIterationSmoothDomain

/-! BKL Corollary 3.7 for the actual normalized iteration. The classical
centered derivatives represent the genuine centered graph gradient, and the
normalization in the Taylor recursion is the literal successor scale. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedFamilyCenteredGradient_ae_of_representative
    (hφ : ContDiff ℝ 1 φ) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (ji : Fin n × ι) :
    (weightedFamilyCenteredGradient φ ι U ji : Space n → ℝ)
      =ᵐ[potentialMeasure φ] weightedCenteredGradientCoordinate φ (f ji.2) ji.1 := by
  have hd : coordinateDerivative (f ji.2) ji.1 =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ ji.1 (U ji.2) : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative hφ (U ji.2) (hf ji.2) (hv ji.2) ji.1)
  have hi := integral_congr_ae hd
  rcases ji with ⟨j, i⟩
  rw [weightedFamilyCenteredGradient_apply]
  filter_upwards [CenteredL2.center_ae (potentialMeasure φ) (weightedH1Derivative φ j (U i)), hd]
    with x hx hy
  rw [hx]
  change _ = coordinateDerivative (f i) j x - ∫ y, coordinateDerivative (f i) j y ∂potentialMeasure φ
  rw [hy, hi]

variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))

include hF hV

/-- The actual Poisson equation transfers every Taylor order through the
literal scale, with no nonzero-scale division or omitted zero branch. -/
theorem weightedIteration_diffusion_taylor_recursion (k d : ℕ)
    (ji : Fin n × WeightedIterationIndex n ι k) (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ (F (k + 1) ji)) d a =
      weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) *
          exponentialTiltCoordinateTaylor φ (weightedCenteredGradientCoordinate φ (F k ji.2) ji.1) d a := by
  have hm := weightedH1_memLp_coordinateDerivative_of_representative (hφ.of_le (by simp))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k ji.2)
      ((hF k ji.2).of_le (by simp)) (hV k ji.2) ji.1
  have hc : MemLp (weightedCenteredGradientCoordinate φ (F k ji.2) ji.1) 2 (potentialMeasure φ) :=
    hm.sub (memLp_const _)
  have he : -weightedDiffusion φ (F (k + 1) ji) = fun x =>
      weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) *
          weightedCenteredGradientCoordinate φ (F k ji.2) ji.1 x := by
    funext x
    have hp := weightedIteration_smooth_successor_equation hφ hκ hlower U F hF hV k ji x
    change -weightedDiffusion φ (F (k + 1) ji) x = _
    unfold weightedCenteredGradientCoordinate
    linarith only [hp]
  rw [he]
  exact exponentialTiltCoordinateTaylor_const_mul (hφ.of_le (by simp)) hκ hlower hc _ d a

/-- Literal coordinate/family Corollary 3.7. Taylor indices precede the
new gradient index; every original component ji is held fixed by the average. -/
theorem weightedIteration_centered_taylor_recursion
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    (k : ℕ) {d : ℕ} (hd : d ≠ 0)
    (ji : Fin n × WeightedIterationIndex n ι k) (a : Fin (d + 1) → Fin n) :
    (∑ σ : Equiv.Perm (Fin (d + 1)),
        exponentialTiltCenteredGradientTaylor φ (F (k + 1) ji) d (a ∘ σ)) / (d + 1).factorial =
      weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) *
          exponentialTiltCoordinateTaylor φ (weightedCenteredGradientCoordinate φ (F k ji.2) ji.1)
            (d + 1) a := by
  have hG := weightedH1_integrable_gradient_norm_sq_of_representative (hφ.of_le (by simp))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (k + 1) ji)
      ((hF (k + 1) ji).of_le (by simp)) (hV (k + 1) ji)
  calc
    _ = exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ (F (k + 1) ji)) (d + 1) a :=
      (weightedDiffusion_exponentialTilt_centered_taylor_tensor (hφ.of_le (by simp)) hκ hlower
        ((hF (k + 1) ji).of_le (by simp)) (hL (k + 1) ji) hG hd a).symm
    _ = _ := weightedIteration_diffusion_taylor_recursion hφ hκ hlower U F hF hV k (d + 1) ji a

end KLS
end

#print axioms KLS.weightedFamilyCenteredGradient_ae_of_representative
#print axioms KLS.weightedIteration_diffusion_taylor_recursion
#print axioms KLS.weightedIteration_centered_taylor_recursion
