import KLS.WeightedMassResolventBochner
import KLS.WeightedResolventGradientMaximum

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Under an actual smooth convex potential, the true smooth resolvent
preserves the forcing's global gradient bound. Its solution, gradient energy,
Hessian integrability, and vanishing cutoff argument are all constructed. -/
theorem weightedMassResolvent_exists_gradient_bounded_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ ∧
      (∀ x, f x-t*weightedDiffusion φ f x=g x) ∧ ∀ x, ‖gradient f x‖ ≤ M := by
  obtain ⟨f,hf,hf2,hd,_,hfμ,hm,heq⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hLval (x : Space n) : weightedDiffusion φ f x=t⁻¹*(f x-g x) := by
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [heq x]
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    rw [show weightedDiffusion φ f = fun x => t⁻¹*(f x-g x) from funext hLval]
    exact (hf2.sub hg2).const_mul _
  have hG := integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  have hbound := norm_gradient_le_of_resolvent_diffusion_domain hφ2
    (hf.of_le (by simp)) (hg.of_le (by simp)) ht heq
    (hessianGradientForm_nonneg_of_convex hφ2 hconv f) hL hG hM hgM
  exact ⟨f,hf,hf2,hd,hfμ,hm,heq,hbound⟩

/-- The same constructed representative has the literal global Lipschitz
constant supplied for the forcing gradient. -/
theorem weightedMassResolvent_exists_lipschitz_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    (M : ℝ≥0) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      LipschitzWith M f ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ ∧
      ∀ x, f x-t*weightedDiffusion φ f x=g x := by
  obtain ⟨f,hf,hf2,_,hfμ,hm,heq,hbound⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hg hg2
      M.coe_nonneg hgM
  have hlip : LipschitzWith M f := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
    intro x
    change ‖fderiv ℝ f x‖ ≤ (M : ℝ)
    rw [← norm_gradient_eq_norm_fderiv]
    exact hbound x
  exact ⟨f,hf,hf2,hlip,hfμ,hm,heq⟩

end KLS
end
