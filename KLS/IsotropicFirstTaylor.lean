import KLS.WeightedTaylorFirstMoment
import KLS.IsotropicAffineL2

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace BigOperators

noncomputable section
namespace KLS
variable {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
  (hiso : IsIsotropic (potentialMeasure V))

include hV hκ hlower hiso

/-- Every actual order-one coefficient is the corresponding coordinate
inner product, for arbitrary L2 observables without a centering premise. -/
theorem exponentialTiltCoordinateTaylor_one_of_isotropic
    (f : Lp ℝ 2 (potentialMeasure V)) (a : Fin 1 → Fin n) :
    exponentialTiltCoordinateTaylor V f 1 a =
      inner ℝ (isotropicAffineCoordinate hiso (some (a 0))) f := by
  let m := ∫ x, f x ∂potentialMeasure V
  have hf := Lp.memLp f
  have hg : MemLp (fun x => f x - m) 2 (potentialMeasure V) :=
    hf.sub (memLp_const m)
  have hm : (∫ x, f x - m ∂potentialMeasure V) = 0 := by
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have he := exponentialTiltCoordinateTaylor_one_of_integral_eq_zero
    hV hκ hlower hg hm a
  rw [exponentialTiltCoordinateTaylor_sub_const hV hκ hlower hf m (by decide)] at he
  rw [he, inner_isotropicAffineCoordinate]
  have hfi := hf.integrable_mul (hiso.memLp_coordinate (a 0))
  change Integrable (fun x => f x * x (a 0)) (potentialMeasure V) at hfi
  have hmi := (hiso.memLp_coordinate (a 0)).integrable (by norm_num)
  simp_rw [sub_mul]
  rw [integral_sub hfi (hmi.const_mul m), integral_const_mul, hiso.integral_coordinate]
  simp only [mul_zero, sub_zero, affineCoordinateFunction, Option.elim_some]
  exact integral_congr_ae (.of_forall fun _ => mul_comm _ _)

/-- The entire degree-one coordinate tensor has the norm of the actual
coordinate projection vector. -/
theorem sum_exponentialTiltCoordinateTaylor_one_sq_eq
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 1 → Fin n, exponentialTiltCoordinateTaylor V f 1 a ^ 2) =
      ‖affineProjectionVector hiso f‖ ^ 2 := by
  simp_rw [exponentialTiltCoordinateTaylor_one_of_isotropic hV hκ hlower hiso]
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun _ => rfl)

/-- An exact Pythagorean identity isolates the affine-orthogonal remainder.
It implies that the sharp degree-one tensor bound needs no cumulant premise. -/
theorem sum_exponentialTiltCoordinateTaylor_one_sq_add_remainder
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 1 → Fin n, exponentialTiltCoordinateTaylor V f 1 a ^ 2) +
      ‖finiteOrthonormalRemainder (isotropicAffineCoordinate hiso) f‖ ^ 2 =
        ProbabilityTheory.variance f (potentialMeasure V) := by
  rw [sum_exponentialTiltCoordinateTaylor_one_sq_eq hV hκ hlower hiso]
  have hp := finiteOrthonormalProjection_remainder_norm_sq
    (orthonormal_isotropicAffineCoordinate hiso) f
  rw [finiteOrthonormalProjection_norm_sq (orthonormal_isotropicAffineCoordinate hiso),
    Fintype.sum_option] at hp
  have hm : inner ℝ (isotropicAffineCoordinate hiso none) f =
      ∫ x, f x ∂potentialMeasure V := by
    rw [inner_isotropicAffineCoordinate]
    simp only [affineCoordinateFunction, Option.elim_none, one_mul]
  have hn : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂potentialMeasure V := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  rw [hm, hn] at hp
  rw [ProbabilityTheory.variance_eq_sub (Lp.memLp f), EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hiso (some j)) f ^ 2) + _ = _
  simpa only [Pi.pow_apply] using (eq_sub_iff_add_eq.mpr (by linarith [hp]))

/-- The first-order tensor is controlled by actual variance, including
arbitrary noncentered L2 observables. -/
theorem sum_exponentialTiltCoordinateTaylor_one_sq_le_variance
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 1 → Fin n, exponentialTiltCoordinateTaylor V f 1 a ^ 2) ≤
      ProbabilityTheory.variance f (potentialMeasure V) := by
  have he := sum_exponentialTiltCoordinateTaylor_one_sq_add_remainder hV hκ hlower hiso f
  linarith [sq_nonneg ‖finiteOrthonormalRemainder (isotropicAffineCoordinate hiso) f‖]

/-- The full L2 order-one bound has the dimension-free sharp constant one. -/
theorem sum_exponentialTiltCoordinateTaylor_one_sq_le_norm
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 1 → Fin n, exponentialTiltCoordinateTaylor V f 1 a ^ 2) ≤ ‖f‖ ^ 2 := by
  rw [sum_exponentialTiltCoordinateTaylor_one_sq_eq hV hκ hlower hiso]
  have ha := affineProjectionVector_norm_sq_le hiso f
  have hp := finiteOrthonormalProjection_remainder_norm_sq
    (orthonormal_isotropicAffineCoordinate hiso) f
  nlinarith [sq_nonneg ‖finiteOrthonormalRemainder (isotropicAffineCoordinate hiso) f‖]

/-- A normalized coordinate attains the degree-one bound in every
nonzero coordinate direction, certifying that its constant one is sharp. -/
theorem sum_exponentialTiltCoordinateTaylor_one_sq_coordinate (i : Fin n) :
    (∑ a : Fin 1 → Fin n,
      exponentialTiltCoordinateTaylor V (isotropicAffineCoordinate hiso (some i)) 1 a ^ 2) = 1 ∧
      ‖isotropicAffineCoordinate hiso (some i)‖ = 1 := by
  refine ⟨?_, (orthonormal_isotropicAffineCoordinate hiso).norm_eq_one (some i)⟩
  rw [sum_exponentialTiltCoordinateTaylor_one_sq_eq hV hκ hlower hiso,
    EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hiso (some j))
    (isotropicAffineCoordinate hiso (some i)) ^ 2) = 1
  simp only [orthonormal_iff_ite.mp (orthonormal_isotropicAffineCoordinate hiso),
    Option.some.injEq, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
  simp

/-- For a radius at least one, the genuine universal scalar Taylor criterion
has exactly the remaining degrees two and above. -/
theorem weightedCoordinateTaylorBound_iff_order_ge_two {R : ℝ} (hR : 1 ≤ R) :
    WeightedCoordinateTaylorBound V R ↔
      ∀ d : ℕ, 2 ≤ d → ∀ f : Lp ℝ 2 (potentialMeasure V),
        (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
          R ^ (2 * d) * ‖f‖ ^ 2 := by
  constructor
  · intro h d hd f
    exact h d (by omega) f
  · intro h d hd f
    by_cases hd2 : 2 ≤ d
    · exact h d hd2 f
    have he : d = 1 := by omega
    subst d
    have hR2 : 1 ≤ R ^ (2 * 1) := one_le_pow₀ hR
    exact (sum_exponentialTiltCoordinateTaylor_one_sq_le_norm hV hκ hlower hiso f).trans
      (by nlinarith [sq_nonneg ‖f‖])

end KLS
end
