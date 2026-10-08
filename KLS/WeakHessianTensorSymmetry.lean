import KLS.WeakMixedDerivativeSymmetry

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma locallyLipschitz_coordinateDerivative_of_gradient
    {u : Space n → ℝ} (hG : LocallyLipschitz (gradient u)) (i : Fin n) :
    LocallyLipschitz (coordinateDerivative u i) := by
  have he : coordinateDerivative u i = fun x => gradient u x i :=
    funext (coordinateDerivative_eq_gradient u i)
  rw [he]
  exact ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).lipschitzWith.locallyLipschitz).comp hG

lemma locallyIntegrable_coordinateDerivative_of_locallyLipschitz
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (i : Fin n) :
    LocallyIntegrable (coordinateDerivative f i) volume := by
  apply locallyIntegrable_of_memLp_two_on_compacts
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (memLp_top_coordinateDerivative_of_locallyLipschitz hf i hK).mono_exponent (by simp)

/-- The actual Hessian is the weak derivative of the actual first gradient
whenever that gradient is locally Lipschitz. -/
theorem actual_hessian_hasLocalWeakCoordinateDerivative
    {u : Space n → ℝ} (hG : LocallyLipschitz (gradient u)) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (coordinateDerivative u j)
      (fun x => coordinateHessian u x i j) i :=
  hasLocalWeakCoordinateDerivative_of_locallyLipschitz
    (locallyLipschitz_coordinateDerivative_of_gradient hG j) i

/-- Hessian symmetry follows by commuting genuine weak derivatives. -/
theorem actual_hessian_ae_symmetric_of_locallyLipschitz_gradient
    {u : Space n → ℝ} (hu : LocallyLipschitz u) (hG : LocallyLipschitz (gradient u)) :
    ∀ᵐ x, (coordinateHessian u x).IsSymm := by
  have he (i j : Fin n) : (fun x => coordinateHessian u x i j) =ᵐ[volume]
      (fun x => coordinateHessian u x j i) :=
    weak_mixed_coordinateDerivatives_commute
      (hasLocalWeakCoordinateDerivative_of_locallyLipschitz hu j)
      (hasLocalWeakCoordinateDerivative_of_locallyLipschitz hu i)
      (actual_hessian_hasLocalWeakCoordinateDerivative hG i j)
      (actual_hessian_hasLocalWeakCoordinateDerivative hG j i)
      (locallyIntegrable_coordinateDerivative_of_locallyLipschitz
        (locallyLipschitz_coordinateDerivative_of_gradient hG j) i)
      (locallyIntegrable_coordinateDerivative_of_locallyLipschitz
        (locallyLipschitz_coordinateDerivative_of_gradient hG i) j)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with x hx
  exact Matrix.IsSymm.ext (fun i j => hx j i)

/-- The raw locally L2 third tensor of the actual Hessian is symmetric in
both adjacent pairs. It is not identified with a classical third derivative. -/
theorem actual_weak_third_tensor_ae_symmetric
    {u : Space n → ℝ} {T : Space n → Fin n → Fin n → Fin n → ℝ}
    (hu : LocallyLipschitz u) (hG : LocallyLipschitz (gradient u))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k) :
    ∀ᵐ x, ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by
  have hloc (k i j : Fin n) : LocallyIntegrable (fun x => T x k i j) volume :=
    locallyIntegrable_of_memLp_two_on_compacts (hTl k i j)
  have hfirst (k i j : Fin n) : (fun x => T x k i j) =ᵐ[volume]
      (fun x => T x i k j) :=
    weak_mixed_coordinateDerivatives_commute
      (actual_hessian_hasLocalWeakCoordinateDerivative hG i j)
      (actual_hessian_hasLocalWeakCoordinateDerivative hG k j)
      (hTw k i j) (hTw i k j) (hloc k i j) (hloc i k j)
  have hsym := actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hu hG
  have hsecond (k i j : Fin n) : (fun x => T x k i j) =ᵐ[volume]
      (fun x => T x k j i) := by
    have he : (fun x => coordinateHessian u x i j) =ᵐ[volume]
        (fun x => coordinateHessian u x j i) := hsym.mono fun x hx => hx.apply j i
    exact ((hTw k i j).congr_ae he Filter.EventuallyEq.rfl).unique
      (hTw k j i) (hloc k i j) (hloc k j i)
  filter_upwards [ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i => ae_all_iff.mpr (hfirst k i))),
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsecond k i)))] with x hx hy
  exact fun k i j => ⟨hx k i j, hy k i j⟩

end KLS
end
