import KLS.QuadraticBarrierStability
import KLS.MomentQuadraticViscosity

/-! Explicit ballwise quadratic-barrier estimates for the original weak
moment transport. The bound uses the ordinary operator norm of the test
matrix action and the actual exponential moment density. -/

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

variable {n : ℕ}

lemma quadratic_part_le_opNorm_radius_sq
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : Space n) {R : ℝ} (hR : 0 ≤ R)
    {x : Space n} (hx : x ∈ closedBall x₀ R) :
    (1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) ≤
      (1 / 2 : ℝ) * ‖matrixAction A‖ * R ^ 2 := by
  have hnorm : ‖x - x₀‖ ≤ R := hx
  have hsq : ‖x - x₀‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hnorm
  calc
    _ ≤ (1 / 2 : ℝ) * (‖x - x₀‖ * ‖matrixAction A (x - x₀)‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖x - x₀‖ * (‖matrixAction A‖ * ‖x - x₀‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((matrixAction A).le_opNorm _) (norm_nonneg _)) (by norm_num)
    _ = (1 / 2 : ℝ) * ‖matrixAction A‖ * ‖x - x₀‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num) (norm_nonneg _))

/-- A proved quantitative nonlinear comparison estimate for the weak moment
potential. Density and boundary data are explicit; no Hessian of u is used. -/
theorem moment_abs_sub_quadratic_le_on_closedBall
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ p : Space n) (c η : ℝ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hboundary : ∀ x ∈ frontier (closedBall x₀ R),
      |u x - centeredQuadratic A x₀ p c x| ≤ η)
    {a b : ℝ} (halow : ((1 - δ) • A).det < a) (hbup : b < ((1 + δ) • A).det)
    (hf : ∀ x ∈ closedBall x₀ R,
      a ≤ Real.exp (-u x + V (gradient u x)) ∧ Real.exp (-u x + V (gradient u x)) ≤ b) :
    ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic A x₀ p c x| ≤ η + (δ / 2) * ‖matrixAction A‖ * R ^ 2 := by
  have hh := abs_sub_quadratic_le_of_alexandrov_density_bounds hLip.continuous hc
    (isCompact_closedBall x₀ R) hA x₀ p c η ((1 / 2 : ℝ) * ‖matrixAction A‖ * R ^ 2)
    hδ hδ1 (fun _ hx => quadratic_part_le_opNorm_radius_sq A x₀ hR hx)
    hboundary halow hbup hf
    (fun S hS _ => subgradient_volume_eq_lintegral_real_moment_density hLip hc hV hK hKc hpush hS)
  intro x hx
  convert hh x hx using 1 <;> ring

end KLS
end

#print axioms KLS.quadratic_part_le_opNorm_radius_sq
#print axioms KLS.moment_abs_sub_quadratic_le_on_closedBall
