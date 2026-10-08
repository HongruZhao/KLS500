import KLS.LocalC11FluxDivergence

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual compact C1,1 cutoff transfers its coefficient-gradient flux
 against any bounded local H1 observable to minus its actual elliptic
 expression. Neither a pairing equality nor observable compactness is assumed. -/
theorem integral_weakEllipticFlux_bounded_local_H1
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ}
    (hA : ∀ i j S, IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j S, IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hdiv : ∀ j ψ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A x i j * coordinateDerivative ψ i x) = ∫ x, b j x * ψ x)
    {χ S : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hDχ : ∀ j, LocallyLipschitz (coordinateDerivative χ j)) (hχc : HasCompactSupport χ)
    (hS : ∀ K : Set (Space n), IsCompact K → MemLp S 2 (volume.restrict K))
    {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖S x‖ ≤ C)
    (hFloc : ∀ i K, IsCompact K → MemLp (F i) 2 (volume.restrict K))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative S (F i) i) :
    (∀ i, Integrable (fun x => weakEllipticFlux A χ i x * F i x)) ∧
    Integrable (fun x => S x * weakEllipticExpression A b χ x) ∧
    (∑ i, ∫ x, weakEllipticFlux A χ i x * F i x) =
      -(∫ x, S x * weakEllipticExpression A b χ x) := by
  have hDzero (x : Space n) (hx : x ∉ tsupport χ) (i : Fin n) : coordinateDerivative χ i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hi => hx (tsupport_coordinateDerivative_subset χ i hi))
  have hHzero (x : Space n) (hx : x ∉ tsupport χ) (i j : Fin n) : coordinateHessian χ x i j = 0 := by
    change coordinateDerivative (coordinateDerivative χ j) i x = 0
    exact image_eq_zero_of_notMem_tsupport (fun hi => hx ((tsupport_coordinateDerivative_subset _ i).trans
      (tsupport_coordinateDerivative_subset χ j) hi))
  have hAzero (i : Fin n) (x : Space n) (hx : x ∉ tsupport χ) : weakEllipticFlux A χ i x = 0 := by
    simp only [weakEllipticFlux,hDzero x hx,mul_zero,Finset.sum_const_zero]
  have hbzero (x : Space n) (hx : x ∉ tsupport χ) : -weakEllipticExpression A b χ x = 0 := by
    simp only [weakEllipticExpression,hDzero x hx,hHzero x hx,mul_zero,Finset.sum_const_zero,
      sub_zero,neg_zero]
  obtain ⟨hi,hbS,he⟩ := integral_divergence_of_bounded_local_H1_test_compact_flux
    (weakEllipticFlux_localL2 hA hDχ)
    (weakEllipticExpression_locallyIntegrable_of_localC11 hA hb hDχ).neg
    (fun _ hψ hc => integral_weakEllipticFlux_coordinateDerivative hA hb hdiv hDχ hψ hc)
    hχc hAzero hbzero hS hbound hFloc hF
  have hpoint : (fun x => (-weakEllipticExpression A b χ x) * S x) =
      fun x => -(S x * weakEllipticExpression A b χ x) := by
    funext x
    ring
  refine ⟨hi,?_,?_⟩
  · convert hbS.neg using 1
    funext x
    dsimp only [Pi.neg_apply]
    ring
  · simpa only [Pi.neg_apply,hpoint,integral_neg] using he

end KLS
end
