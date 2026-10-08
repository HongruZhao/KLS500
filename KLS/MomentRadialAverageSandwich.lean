import KLS.CorrectedRadialAverage
import KLS.DualTransportPairing
import KLS.NormalizedEnergyBound

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A continuous global extension of the actual normalized dual error on the
interior ball. The truncation radius is the original radius plus one. -/
def continuousDualError (u : Space n → ℝ) (c ε T : ℝ) : Space n → ℝ :=
  fun x => -normalizedQuadraticError (truncatedLegendrePotential u (T + 1)) 0 0 (-c) ε x

lemma continuous_continuousDualError {u : Space n → ℝ} (hu : Continuous u)
    (c ε : ℝ) {T : ℝ} (hT : 0 < T) : Continuous (continuousDualError u c ε T) :=
  (((lipschitzWith_truncatedLegendrePotential hu (by linarith : 0 ≤ T + 1)).continuous.sub
    (continuous_centeredQuadratic _ _ _ _)).div_const ε).neg

lemma continuousDualError_eq_dual {u : Space n → ℝ} (hu : Continuous u)
    (hc : StrictConvexOn ℝ univ u) {c ε T M : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hsmall : ε * M ≤ T ^ 2 / 16)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    {x : Space n} (hx : x ∈ ball (0 : Space n) (T / 4)) :
    continuousDualError u c ε T x = normalizedDualQuadraticError u 0 0 c ε x :=
  (normalizedDualQuadraticError_eq_negative_truncated hu hc hT hsmall
    (fun y hy => abs_sub_quadratic_le_of_normalized_bound hε (hbound y hy)) hx).symm

lemma continuousDualError_le_primal {u : Space n → ℝ} (hu : Continuous u)
    (hc : StrictConvexOn ℝ univ u) {c ε T M : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hsmall : ε * M ≤ T ^ 2 / 16)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    {x : Space n} (hx : x ∈ ball (0 : Space n) (T / 4)) :
    continuousDualError u c ε T x ≤ normalizedQuadraticError u 0 0 c ε x := by
  rw [continuousDualError_eq_dual hu hc hε hT hsmall hbound hx]
  exact normalizedDualQuadraticError_le_primal c hε (interior_subset
    (ball_subset_interior_momentLegendreDomain_of_quadratic_closeness hu hc.convexOn hT hsmall
      (fun y hy => abs_sub_quadratic_le_of_normalized_bound hε (hbound y hy)) hx))

lemma ball_subset_centered_ball {c : Space n} {r s R : ℝ}
    (hc : c ∈ closedBall (0 : Space n) r) (hR : r + R ≤ s) :
    ball c R ⊆ ball (0 : Space n) s := by
  intro x hx
  have hh := dist_triangle x c (0 : Space n)
  change dist c 0 ≤ r at hc
  change dist x c < R at hx
  change dist x 0 < s
  linarith

/-- Both genuine radial average inequalities follow from the original weak
moment equation. The errors are explicitly epsilon times the squared radius. -/
theorem moment_radial_average_sandwich (hn : 0 < n)
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {c ε T M t : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) (hT : 0 < T)
    (hsmall : ε * M ≤ T ^ 2 / 16)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) T,
      |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (ht : 0 < t) (htR : t < T / 64)
    {a : Space n} (ha : a ∈ closedBall (0 : Space n) (T / 64)) :
    normalizedQuadraticError u 0 0 c ε a ≤
      (∫ x, normalizedQuadraticError u 0 0 c ε x * radialAverageKernel (normalizedRadialProfile n) a t x) +
        ε * (T / 32) ^ 2 ∧
    (∫ x, continuousDualError u c ε T x * radialAverageKernel (normalizedRadialProfile n) a t x) -
        ε * (T / 32) ^ 2 ≤ continuousDualError u c ε T a ∧
    continuousDualError u c ε T a ≤ normalizedQuadraticError u 0 0 c ε a := by
  have hstrict := moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush
  have has : ball a (T / 64) ⊆ ball (0 : Space n) (T / 16) :=
    ball_subset_centered_ball ha (by linarith)
  have hκs := normalizedRadialKernel_tsupport_subset_centered_closedBall ha ht
    (by linarith : T / 64 + t ≤ T / 32)
  have hcont : Continuous (normalizedQuadraticError u 0 0 c ε) :=
    (hLip.continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const ε
  refine ⟨?_, ?_, continuousDualError_le_primal hLip.continuous hstrict hε hT hsmall hbound
    ((closedBall_subset_ball (by linarith : T / 64 < T / 4)) ha)⟩
  · apply upper_average_of_subharmonic_quadratic_correction hcont hε.le ht htR
      (by positivity) hκs
    intro ψ hψ hψc hψs hψ0
    have hh := moment_integral_subharmonicNormalizedError_mul_laplacian_nonneg hn hLip hc hV
      hK hKc hpush 0 0 c hε hhalf (r := T / 16) (R := T / 8) (by positivity) (by linarith)
      (fun x hx => hdensity x (closedBall_subset_closedBall (by linarith) hx)) hψ hψc (hψs.trans has) hψ0
    simpa only [subharmonicNormalizedError_apply, sub_zero] using hh
  · apply lower_average_of_subharmonic_negative_quadratic_correction
      (continuous_continuousDualError hLip.continuous c ε hT) hε.le ht htR (by positivity) hκs
    intro ψ hψ hψc hψs hψ0
    have hh := moment_integral_subharmonicNegativeDualError_mul_laplacian_nonneg hn hLip hc hV
      hK hKc hpush hε (r := T / 16) (s := T / 8) (by positivity) (by linarith)
      (by linarith) hsmall hbound hdensity hψ hψc (hψs.trans has) hψ0
    convert hh using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport (coordinateLaplacian ψ)
      · have hxU : x ∈ ball (0 : Space n) (T / 4) :=
          ball_subset_ball (by linarith : T / 16 ≤ T / 4) (has (hψs (tsupport_coordinateLaplacian_subset ψ hx)))
        rw [continuousDualError_eq_dual hLip.continuous hstrict hε hT hsmall hbound hxU]
        simp only [subharmonicNegativeDualError, centeredQuadratic, sub_zero, inner_zero_left,
          zero_add, add_zero, matrixAction_one_apply, real_inner_self_eq_norm_sq]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

end KLS
end
