import KLS.WeightedMassResolventSmooth
import KLS.WeightedBochnerDomain

open MeasureTheory InnerProductSpace Filter Matrix
open scoped BigOperators ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Smooth L2 forcing under nonnegative curvature gives an actual resolvent
whose coordinate gradients lie in the faithful finite-energy class. Hessian
integrability and the sharp Bochner identity are derived from its equation. -/
theorem weightedMassResolvent_exists_bochner_representative
    {φ g : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 ≤ κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {t : ℝ} (ht : 0 < t) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ)) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      (∫ x, f x ∂potentialMeasure φ) = ∫ x, g x ∂potentialMeasure φ ∧
      (∀ x, f x - t * weightedDiffusion φ f x = g x) ∧
      MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, LocallyLipschitzTests (potentialMeasure φ) (coordinateDerivative f i) ∧
        energy (potentialMeasure φ) (coordinateDerivative f i) < ⊤) ∧
      (∀ i j : Fin n, MemLp (fun x => coordinateHessian f x i j) 2 (potentialMeasure φ)) ∧
      Integrable (hessianSquare f) (potentialMeasure φ) ∧
      Integrable (hessianGradientForm φ f) (potentialMeasure φ) ∧
      (∫ x, hessianSquare f x ∂potentialMeasure φ) +
        (∫ x, hessianGradientForm φ f x ∂potentialMeasure φ) =
          t⁻¹ ^ 2 * ∫ x, (f x - g x) ^ 2 ∂potentialMeasure φ ∧
      (∫ x, hessianSquare f x ∂potentialMeasure φ) +
        κ * (∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ) ≤
          t⁻¹ ^ 2 * ∫ x, (f x - g x) ^ 2 ∂potentialMeasure φ := by
  obtain ⟨f, hf, hf2, hd, _, hfμ, hm, heq⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  have hLval (x : Space n) : weightedDiffusion φ f x = t⁻¹ * (f x - g x) := by
    have hx := heq x
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    have he : weightedDiffusion φ f = fun x => t⁻¹ * (f x - g x) := funext hLval
    rw [he]
    exact (hf2.sub hg2).const_mul _
  have hG := integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  have hc (x : Space n) : 0 ≤ hessianGradientForm φ f x :=
    (mul_nonneg hκ (sq_nonneg _)).trans (hessianGradientForm_lower_bound hlower x)
  obtain ⟨hH,hC⟩ := integrable_bochner_terms_of_diffusion_domain
    (hφ.of_le (by simp)) (hf.of_le (by simp)) hc hL hG
  have hHij (i j : Fin n) : MemLp (fun x => coordinateHessian f x i j) 2 (potentialMeasure φ) :=
    memLp_coordinateHessian_of_integrable_hessianSquare (hf.of_le (by simp)) hH i j
  have hD (i : Fin n) : LocallyLipschitzTests (potentialMeasure φ) (coordinateDerivative f i) ∧
      energy (potentialMeasure φ) (coordinateDerivative f i) < ⊤ := by
    refine ⟨⟨(contDiff_coordinateDerivative hf (m := 1) (by simp) i).locallyLipschitz,hd i⟩,?_⟩
    exact energy_lt_top_of_memLp_coordinateDerivative (fun j => hHij j i)
  have hLs : (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) =
      t⁻¹ ^ 2 * ∫ x, (f x - g x) ^ 2 ∂potentialMeasure φ := by
    simp_rw [hLval,mul_pow]
    exact integral_const_mul _ _
  have hb := integral_weightedDiffusion_sq_of_L2_domain
    (hφ.of_le (by simp)) (hf.of_le (by simp)) hc hL hG
  have hbκ := integral_hessianSquare_add_curvature_gradient_le_diffusion_sq
    (hφ.of_le (by simp)) (hf.of_le (by simp)) hκ hlower hL hG
  rw [hLs] at hb hbκ
  exact ⟨f,hf,hf2,hfμ,hm,heq,hL,hD,hHij,hH,hC,hb.symm,hbκ⟩

end KLS
end
