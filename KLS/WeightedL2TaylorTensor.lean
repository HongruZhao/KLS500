import KLS.WeightedTiltTaylorLinearity
import KLS.FiniteL2Reindex

/-! The actual coordinate Taylor tensor as a linear map on genuine weighted
L2 families. A separately labeled scalar Taylor bound lifts to finite families;
the scalar bound is a criterion hypothesis and is not asserted globally. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ}

theorem exponentialTiltCoordinateTaylor_congr_ae {φ f g : Space n → ℝ}
    (hfg : f =ᵐ[potentialMeasure φ] g) (d : ℕ) (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor φ f d a = exponentialTiltCoordinateTaylor φ g d a := by
  have he : (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z) =
      fun z => ∫ x, g x ∂exponentialTilt (potentialMeasure φ) z := by
    funext z
    exact integral_congr_ae ((tilted_absolutelyContinuous (potentialMeasure φ) (fun x => inner ℝ z x)).ae_eq hfg)
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [he]

def weightedL2TaylorTensor (φ : Space n → ℝ) (d : ℕ) {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) :
    EuclideanSpace ℝ ((Fin d → Fin n) × ι) :=
  WithLp.toLp 2 (fun ai => exponentialTiltCoordinateTaylor φ (g ai.2) d ai.1)

@[simp] theorem weightedL2TaylorTensor_apply (φ : Space n → ℝ) (d : ℕ)
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι)
    (a : Fin d → Fin n) (i : ι) :
    weightedL2TaylorTensor φ d g (a, i) = exponentialTiltCoordinateTaylor φ (g i) d a := rfl

variable {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2TaylorTensor_sub (d : ℕ) {ι : Type*} [Fintype ι]
    (g h : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedL2TaylorTensor φ d (g - h) = weightedL2TaylorTensor φ d g - weightedL2TaylorTensor φ d h := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  change exponentialTiltCoordinateTaylor φ (g i - h i : Lp ℝ 2 (potentialMeasure φ)) d a =
    exponentialTiltCoordinateTaylor φ (g i) d a - exponentialTiltCoordinateTaylor φ (h i) d a
  rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_sub _ _) d a]
  exact exponentialTiltCoordinateTaylor_sub hφ hκ hlower (Lp.memLp _) (Lp.memLp _) d a

theorem weightedL2TaylorTensor_smul (d : ℕ) {ι : Type*} [Fintype ι]
    (c : ℝ) (g : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedL2TaylorTensor φ d (c • g) = c • weightedL2TaylorTensor φ d g := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  change exponentialTiltCoordinateTaylor φ (c • g i : Lp ℝ 2 (potentialMeasure φ)) d a =
    c * exponentialTiltCoordinateTaylor φ (g i) d a
  rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_smul c _) d a]
  exact exponentialTiltCoordinateTaylor_const_mul hφ hκ hlower (Lp.memLp _) c d a

theorem weightedL2TaylorTensor_add (d : ℕ) {ι : Type*} [Fintype ι]
    (g h : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedL2TaylorTensor φ d (g + h) = weightedL2TaylorTensor φ d g + weightedL2TaylorTensor φ d h := by
  have he := weightedL2TaylorTensor_sub hφ hκ hlower d (g + h) h
  rw [add_sub_cancel_right] at he
  exact eq_add_of_sub_eq he.symm

def weightedL2TaylorLinearMap (d : ℕ) (ι : Type*) [Fintype ι] :
    CenteredL2.Family (potentialMeasure φ) ι →ₗ[ℝ] EuclideanSpace ℝ ((Fin d → Fin n) × ι) where
  toFun := weightedL2TaylorTensor φ d
  map_add' := weightedL2TaylorTensor_add hφ hκ hlower d
  map_smul' := weightedL2TaylorTensor_smul hφ hκ hlower d

/-- The squared literal scalar bound (29), to be supplied as the spectral
criterion hypothesis. For R >= 0 it is equivalent to the ordinary norm bound. -/
def WeightedCoordinateTaylorBound (φ : Space n → ℝ) (R : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ f : Lp ℝ 2 (potentialMeasure φ),
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor φ f d a ^ 2) ≤ R ^ (2 * d) * ‖f‖ ^ 2

omit [IsProbabilityMeasure (potentialMeasure φ)] hφ hκ hlower in
theorem weightedL2TaylorTensor_norm_sq_le {R : ℝ} (hR : WeightedCoordinateTaylorBound φ R)
    {d : ℕ} (hd : 1 ≤ d) {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤ R ^ (2 * d) * ‖g‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hR d hd (g i))

omit [IsProbabilityMeasure (potentialMeasure φ)] hφ hκ hlower in
theorem weightedL2TaylorTensor_norm_le {R : ℝ} (hR0 : 0 ≤ R)
    (hR : WeightedCoordinateTaylorBound φ R) {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedL2TaylorTensor φ d g‖ ≤ R ^ d * ‖g‖ := by
  have he : (R ^ d * ‖g‖) ^ 2 = R ^ (2 * d) * ‖g‖ ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm d 2]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg hR0 _) (norm_nonneg _))).mp
  rw [he]
  exact weightedL2TaylorTensor_norm_sq_le hR hd g

/-- The genuine Taylor family linear map is continuous with norm at most R^d
when the literal scalar bound (29) is supplied. -/
def weightedL2TaylorContinuousLinearMap {R : ℝ} (hR0 : 0 ≤ R)
    (hR : WeightedCoordinateTaylorBound φ R) {d : ℕ} (hd : 1 ≤ d)
    (ι : Type*) [Fintype ι] :
    CenteredL2.Family (potentialMeasure φ) ι →L[ℝ] EuclideanSpace ℝ ((Fin d → Fin n) × ι) :=
  (weightedL2TaylorLinearMap hφ hκ hlower d ι).mkContinuous (R ^ d)
    (weightedL2TaylorTensor_norm_le hR0 hR hd)

end KLS
end

#print axioms KLS.exponentialTiltCoordinateTaylor_congr_ae
#print axioms KLS.weightedL2TaylorLinearMap
#print axioms KLS.weightedL2TaylorTensor_norm_sq_le
#print axioms KLS.weightedL2TaylorContinuousLinearMap
