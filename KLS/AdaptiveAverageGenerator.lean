import KLS.AdaptiveAverageDerivatives

/-! Vanishing generator and the exact normalized Brownian coefficient for law averages. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc KLS.LocalDiffusion
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem integrable_law_of_integrable (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (p : Parameter n) : Integrable f (law μ p.1 p.2) :=
  integrable_tilted_of_compact_support hμ (continuous_exponent p.1 p.2) hf

theorem coordinateScore_diffusion (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    coordinateScore (coordinateDiffusion μ k z) = projection μ (decodeState z) k := by
  unfold coordinateScore coordinateDiffusion
  rw [decode_encodeState]
  exact exponent_diffusion_eq_projection _ _

theorem coordinateScore_drift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    coordinateScore (coordinateDrift μ z) = fun x => ∑ k : Fin n,
      (coordinateAverage μ (projection μ (decodeState z) k) z * projection μ (decodeState z) k x -
        (projection μ (decodeState z) k x)^2/2) := by
  unfold coordinateScore coordinateDrift
  rw [decode_encodeState, exponent_drift_eq_projection_sum hμ hfull]
  funext x
  apply Finset.sum_congr rfl
  intro k _
  change coordinateAverage μ (projection μ (decodeState z) k) z * _ + (-_ / 2) = _
  ring

theorem coordinateAverage_drift_score (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z : Fin (n+n*n) → ℝ) :
    coordinateAverage μ (fun x => f x * ∑ k : Fin n,
      (coordinateAverage μ (projection μ (decodeState z) k) z * projection μ (decodeState z) k x -
        (projection μ (decodeState z) k x)^2/2)) z =
      ∑ k : Fin n,
        (coordinateAverage μ (projection μ (decodeState z) k) z *
          coordinateAverage μ (fun x => f x * projection μ (decodeState z) k x) z -
        coordinateAverage μ (fun x => f x * (projection μ (decodeState z) k x)^2) z / 2) := by
  let p := decodeState z
  let h := projection μ p
  have hi (k : Fin n) : Integrable (fun x => f x * h k x) (law μ p.1 p.2) :=
    integrable_law_of_integrable hμ
      (integrable_mul_continuous_of_compact_support hμ hf (continuous_projection p k)) p
  have hi2 (k : Fin n) : Integrable (fun x => f x * (h k x)^2) (law μ p.1 p.2) :=
    integrable_law_of_integrable hμ
      (integrable_mul_continuous_of_compact_support hμ hf ((continuous_projection p k).pow 2)) p
  have he : (fun x => f x * ∑ k : Fin n, (coordinateAverage μ (h k) z * h k x - (h k x)^2/2)) =
      fun x => ∑ k : Fin n, (coordinateAverage μ (h k) z * (f x*h k x) - (f x*(h k x)^2)/2) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∫ x, f x * ∑ k : Fin n, (_ * h k x - _) ∂law μ p.1 p.2) = _
  have hfin (k : Fin n) : Integrable (fun x => coordinateAverage μ (h k) z * (f x*h k x) - (f x*(h k x)^2)/2) (law μ p.1 p.2) :=
    ((hi k).const_mul _).sub ((hi2 k).div_const 2)
  rw [he, integral_finsetSum Finset.univ (fun k _ => hfin k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sub ((hi k).const_mul _) ((hi2 k).div_const 2), integral_const_mul, integral_div]
  rfl

/-- Actual tilted averages have zero generator for the adaptive parameter SDE. -/
theorem coordinateAverage_generator_zero (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) {f : Space n → ℝ} (hf : Integrable f μ)
    (z : Fin (n+n*n) → ℝ) :
    coordinateAverageGradient μ f z (coordinateDrift μ z) +
      1/2 * ∑ k : Fin n, coordinateAverageHessian μ f z
        (coordinateDiffusion μ k z) (coordinateDiffusion μ k z) = 0 := by
  rw [coordinateAverageGradient_apply hμ hf, coordinateScore_drift hμ hfull,
    coordinateAverage_drift_score hμ hf]
  have h1 := coordinateAverage_drift_score hμ (integrable_const (1 : ℝ)) z
  simp only [one_mul] at h1
  rw [h1, Finset.mul_sum]
  simp_rw [coordinateAverageHessian_apply_self hμ hf, coordinateScore_diffusion]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  ring

open KLS.LocalDiffusion in
/-- Exact coordinate form consumed by the local Itô theorem. -/
theorem observableGenerator_coordinateAverage (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) {f : Space n → ℝ} (hf : Integrable f μ)
    (z : Fin (n+n*n) → ℝ) :
    observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateAverageGradient μ f) (coordinateAverageHessian μ f) z = 0 := by
  have h := coordinateAverage_generator_zero hμ hfull hf z
  rw [apply_eq_sum_coordDeriv] at h
  simp_rw [apply₂_eq_sum_coordDeriv₂] at h
  unfold observableGenerator
  have hd : (∑ a : Fin (n+n*n), coordDeriv (coordinateAverageGradient μ f) a z * coordinateDrift μ z a) =
      ∑ a : Fin (n+n*n), coordinateDrift μ z a * coordDeriv (coordinateAverageGradient μ f) a z :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hd]
  convert h using 1
  congr 1
  congr 1
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  ring

def averageNoiseCoefficient (μ : Measure (Space n)) (f : Space n → ℝ) (k : Fin n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  coordinateAverageGradient μ f z (coordinateDiffusion μ k z)

/-- Paper (68): the genuine diffusion coefficient is the normalized centered integral. -/
theorem averageNoiseCoefficient_eq_integral (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    averageNoiseCoefficient μ f k z =
      ∫ x, f x * normalizedCenteredVector (law μ (decodeState z).1 (decodeState z).2) x k
        ∂law μ (decodeState z).1 (decodeState z).2 := by
  rw [averageNoiseCoefficient, coordinateAverageGradient_apply hμ hf, coordinateScore_diffusion]
  simp_rw [← projection_sub_average_eq_normalized hμ]
  have hf' := integrable_law_of_integrable hμ hf (decodeState z)
  have hfp := integrable_law_of_integrable hμ
    (integrable_mul_continuous_of_compact_support hμ hf (continuous_projection (μ := μ) (decodeState z) k))
    (decodeState z)
  simp_rw [mul_sub]
  rw [integral_sub hfp (hf'.mul_const _), integral_mul_const]
  rfl

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateAverage_generator_zero
#print axioms KLS.AdaptiveLocalization.averageNoiseCoefficient_eq_integral
