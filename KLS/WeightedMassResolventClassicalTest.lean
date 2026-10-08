import KLS.WeightedMassResolventFaithfulTest

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- A classical representative of the actual full resolvent has the actual
centered graph derivatives; restoring the mean adds no derivative. -/
theorem weightedMassResolvent_coordinateDerivative_of_representative
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfμ : f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i (weightedResolventH1 φ ht g) : Space n → ℝ) := by
  have hcenter : (fun x => f x - ∫ y, g y ∂potentialMeasure φ) =ᵐ[potentialMeasure φ]
      (weightedH1Value φ (weightedResolventH1 φ ht g) : Space n → ℝ) := by
    filter_upwards [hfμ, weightedMassResolvent_ae ht g] with x hx hy
    change f x - _ = weightedResolvent φ ht g x
    rw [hx, hy]
    ring
  have hv := (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq hcenter
  have hd := weightedH1_coordinateDerivative_of_representative hφ (weightedResolventH1 φ ht g)
    (hf.sub contDiff_const) hv i
  have heq : coordinateDerivative (fun x => f x - ∫ y, g y ∂potentialMeasure φ) i =
      coordinateDerivative f i := by
    funext x
    simp only [coordinateDerivative, fderiv_sub_const]
  rw [heq] at hd
  exact (withDensity_absolutelyContinuous _ _).ae_eq hd

/-- The literal classical gradient pairing holds for all faithful finite-energy tests.
Its equation is derived from the constructed resolvent, not supplied as a premise. -/
theorem weightedMassResolvent_classical_faithful_test
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfμ : f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    (∫ x, f x * ψ x ∂potentialMeasure φ) +
      t * (∑ i : Fin n, ∫ x, coordinateDerivative f i x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ := by
  have he := weightedMassResolvent_faithful_test hφ.continuous ht g hψ heψ
  have hv : (∫ x, weightedMassResolvent φ ht g x * ψ x ∂potentialMeasure φ) =
      ∫ x, f x * ψ x ∂potentialMeasure φ :=
    integral_congr_ae (hfμ.symm.mul EventuallyEq.rfl)
  have hd (i : Fin n) : (∫ x,
      weightedH1Derivative φ i (weightedResolventH1 φ ht g) x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) =
      ∫ x, coordinateDerivative f i x * coordinateDerivative ψ i x ∂potentialMeasure φ :=
    integral_congr_ae ((weightedMassResolvent_coordinateDerivative_of_representative
      hφ ht g hf hfμ i).symm.mul EventuallyEq.rfl)
  simpa only [hv, hd] using he

end KLS
end
