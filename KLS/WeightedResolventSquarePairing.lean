import KLS.WeightedResolventMixedSmoothing

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

omit [IsProbabilityMeasure (potentialMeasure φ)] in
/-- An actual weighted L2 pairing with a faithful function is its literal integral. -/
theorem weighted_inner_toLp_eq_integral {ψ : Space n → ℝ}
    (hψ : MemLp ψ 2 (potentialMeasure φ)) (g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ g (hψ.toLp ψ) = ∫ x, g x*ψ x ∂potentialMeasure φ := by
  rw [L2.real_inner_eq_integral]
  exact integral_congr_ae (EventuallyEq.rfl.mul hψ.coeFn_toLp)

/-- The actual variational equation and squared resolvent identity yield the
literal gradient pairing, including its integration-by-parts minus sign. -/
theorem weightedMassResolvent_square_sub_inner_eq
    (hφ : ContDiff ℝ 1 φ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {h : Space n → ℝ} (hh : ContDiff ℝ 1 h)
    (hhμ : h =ᵐ[potentialMeasure φ] (weightedMassResolvent φ hs (weightedMassResolvent φ ht
      (weightedMassResolvent φ ht g + weightedMassResolvent φ hs g)) : Space n → ℝ))
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    inner ℝ (weightedMassResolvent φ ht (weightedMassResolvent φ ht g)-
      weightedMassResolvent φ hs (weightedMassResolvent φ hs g)) (hψ.2.toLp ψ) =
      -(t-s)*(∑ i : Fin n, ∫ x, coordinateDerivative h i x*coordinateDerivative ψ i x
        ∂potentialMeasure φ) := by
  let q := weightedMassResolvent φ ht (weightedMassResolvent φ ht g + weightedMassResolvent φ hs g)
  have hv := weightedMassResolvent_classical_faithful_test hφ hs q hh hhμ hψ heψ
  have hhi : (∫ x, h x*ψ x ∂potentialMeasure φ) =
      inner ℝ (weightedMassResolvent φ hs q) (hψ.2.toLp ψ) := by
    rw [weighted_inner_toLp_eq_integral]
    exact integral_congr_ae (hhμ.mul EventuallyEq.rfl)
  rw [hhi,← weighted_inner_toLp_eq_integral hψ.2 q] at hv
  have ha := weightedMassResolvent_square_sub_identity hφ.continuous hs ht g
  rw [weightedMassResolvent_commute hφ.continuous hs ht] at ha
  have hp := congrArg (fun u : Lp ℝ 2 (potentialMeasure φ) => inner ℝ u (hψ.2.toLp ψ)) ha
  simp only [inner_smul_left,conj_trivial,inner_sub_left] at hp
  change s*(inner ℝ (weightedMassResolvent φ ht (weightedMassResolvent φ ht g)) (hψ.2.toLp ψ)-
    inner ℝ (weightedMassResolvent φ hs (weightedMassResolvent φ hs g)) (hψ.2.toLp ψ)) =
      (t-s)*(inner ℝ (weightedMassResolvent φ hs q) (hψ.2.toLp ψ)-inner ℝ q (hψ.2.toLp ψ)) at hp
  rw [inner_sub_left]
  apply (mul_left_cancel₀ hs.ne')
  nlinarith

end KLS
end
