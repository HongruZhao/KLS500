import KLS.WeightedResolventSmoothRepresentative

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The constructed full mass-preserving resolvent has a globally smooth
representative solving the literal equation f - t L_phi f = g. -/
theorem weightedMassResolvent_exists_smooth_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ)) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) ∧
      f =ᵐ[volume] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ ∧
      ∀ x, f x - t * weightedDiffusion φ f x = g x := by
  obtain ⟨u, hu, hu2, _, hdu, _, huμ, heq⟩ :=
    weightedResolvent_exists_smooth_representative hφ ht hg hg2
  let m := ∫ y, g y ∂potentialMeasure φ
  let f := fun x => u x + m
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hu.add contDiff_const
  have hf2 : MemLp f 2 (potentialMeasure φ) := hu2.add (memLp_const m)
  have hd (i : Fin n) : coordinateDerivative f i = coordinateDerivative u i := by
    funext x
    change coordinateDerivative (u + fun _ => m) i x = _
    rw [coordinateDerivative_add (hu.differentiable (by simp) x) (differentiableAt_const m)]
    simp [coordinateDerivative]
  have hm : (∫ y, hg2.toLp g y ∂potentialMeasure φ) = m := integral_congr_ae hg2.coeFn_toLp
  have hfμ : f =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) := by
    filter_upwards [huμ, weightedMassResolvent_ae ht (hg2.toLp g)] with x hx hy
    dsimp only [f]
    rw [hx, hy, hm, add_comm]
  have hfm : (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ := by
    rw [integral_congr_ae hfμ, weightedMassResolvent_integral hφ.continuous ht]
    exact integral_congr_ae hg2.coeFn_toLp
  have hc : ∀ x, weightedDiffusion φ (fun _ : Space n => m) x = 0 := by
    intro x
    have hdconst (i : Fin n) : coordinateDerivative (fun _ : Space n => m) i = 0 := by
      funext y
      simp [coordinateDerivative]
    simp [weightedDiffusion_eq_sum, coordinateHessian, hdconst, coordinateDerivative]
  have hLf (x : Space n) : weightedDiffusion φ f x = weightedDiffusion φ u x := by
    change weightedDiffusion φ (u + fun _ => m) x = _
    rw [weightedDiffusion_add (hu.of_le (by simp)) contDiff_const, hc, add_zero]
  refine ⟨f, hf, hf2, fun i => ?_,
    (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq hfμ, hfμ, hfm, ?_⟩
  · rw [hd]
    exact hdu i
  · intro x
    rw [hLf]
    dsimp only [f, m]
    linarith [heq x]

end KLS
end
