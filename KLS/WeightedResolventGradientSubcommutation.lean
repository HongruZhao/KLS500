import KLS.WeightedGradientSubsolutionComparison

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Actual squared-gradient subcommutation for the true L2 resolvent.
The source's squared gradient is explicitly in L2, and both resolvents,
all graph domains, Hessian integrability, and comparison are constructed. -/
theorem weightedMassResolvent_exists_gradient_subcommutation_pair
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    (hG2 : MemLp (fun x => ‖gradient g x‖ ^ 2) 2 (potentialMeasure φ)) :
    ∃ f v : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      MemLp f 2 (potentialMeasure φ) ∧ MemLp v 2 (potentialMeasure φ) ∧
      f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
      v =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht (hG2.toLp (fun x => ‖gradient g x‖ ^ 2)) : Space n → ℝ) ∧
      (∀ x, f x-t*weightedDiffusion φ f x=g x) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=‖gradient g x‖ ^ 2) ∧
      ∀ x, ‖gradient f x‖ ^ 2 ≤ v x := by
  obtain ⟨f,hf,hf2,hd,_,hfμ,_,heq⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hg hg2
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖gradient g x‖ ^ 2) :=
    contDiff_gradient_norm_sq hg (by simp)
  obtain ⟨v,hv,hv2,hdv,_,hvμ,_,hev⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hG hG2
  have hLval (x : Space n) : weightedDiffusion φ f x=t⁻¹*(f x-g x) := by
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [heq x]
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    rw [show weightedDiffusion φ f = fun x => t⁻¹*(f x-g x) from funext hLval]
    exact (hf2.sub hg2).const_mul _
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact ⟨f,v,hf,hv,hf2,hv2,hfμ,hvμ,heq,hev,
    gradient_norm_sq_le_of_resolvent_equations hφ2 hf (hg.of_le (by simp))
      (hv.of_le (by simp)) ht heq hev (hessianGradientForm_nonneg_of_convex hφ2 hconv f)
      hL hd (hv2.integrable (by norm_num)) hgv⟩

end KLS
end
