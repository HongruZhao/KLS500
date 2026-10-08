import KLS.WeightedResolventPoissonTest

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Moving the actual solution value into the positive zeroth-order coefficient
makes the actual centered resolvent an ordinary local elliptic solution. -/
theorem weightedResolvent_localWeakSol (hφ : ContDiff ℝ 3 φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ} (hg : MemLp g 2 (potentialMeasure φ)) :
    LocalWeakSol univ (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
      (fun x i => coordinateDerivative φ i x) (fun _ => t⁻¹)
      (fun x => t⁻¹ * (g x - ∫ y, g y ∂potentialMeasure φ))
      (weightedH1Value φ (weightedResolventH1 φ ht (hg.toLp g)))
      (fun i => weightedH1Derivative φ i (weightedResolventH1 φ ht (hg.toLp g))) := by
  let U := weightedResolventH1 φ ht (hg.toLp g)
  have hw := weighted_poisson_localWeakSol hφ (U := U)
    (fun ψ hψ hc => weightedResolvent_poisson_test_toLp hφ.continuous ht hg hψ hc)
  intro ψ hψ hc hsub
  have h := hw ψ hψ hc hsub
  simp only [Measure.restrict_univ, zero_mul, integral_zero, add_zero] at h ⊢
  have hgloc := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure hg hφ.continuous
  have huloc := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
    (Lp.memLp (weightedH1Value φ U)) hφ.continuous
  have hgψ : Integrable (fun x => g x * ψ x) volume := by
    simpa only [smul_eq_mul] using
      hgloc.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have huψ : Integrable (fun x => weightedH1Value φ U x * ψ x) volume := by
    simpa only [smul_eq_mul] using
      huloc.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hmψ : Integrable (fun x => (∫ y, g y ∂potentialMeasure φ) * ψ x) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul _
  have hsplit : (∫ x, (t⁻¹ * (g x - (∫ y, g y ∂potentialMeasure φ) -
      weightedH1Value φ U x)) * ψ x) =
      (∫ x, (t⁻¹ * (g x - ∫ y, g y ∂potentialMeasure φ)) * ψ x) -
        ∫ x, t⁻¹ * weightedH1Value φ U x * ψ x := by
    simp_rw [mul_assoc, sub_mul]
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub (f := fun x => g x * ψ x - (∫ y, g y ∂potentialMeasure φ) * ψ x)
        (g := fun x => weightedH1Value φ U x * ψ x) (hgψ.sub hmψ) huψ]
    ring
  rw [hsplit] at h
  change _ + _ + (∫ x, t⁻¹ * weightedH1Value φ U x * ψ x) = _
  linarith

end KLS
end
