import ResolventGradientL1Comparison

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- L1 gradient subcommutation in its smooth positive regularized form, for an
existing actual resolvent representative. The comparison function, graph
integrability, and pointwise equation are all constructed from that resolver. -/
theorem weightedMassResolvent_regularized_gradient_subcommutation
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) {f g : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgrad : MemLp (gradient g) 2 (potentialMeasure φ))
    (hfμ : f =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ))
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x) :
    ∃ v : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      MemLp v 2 (potentialMeasure φ) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative v i) 2 (potentialMeasure φ)) ∧
      v =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht
          ((regularizedGradientNorm_memLp hε hg hgrad).toLp (regularizedGradientNorm ε g)) :
          Space n → ℝ) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=regularizedGradientNorm ε g x) ∧
      ∀ x, regularizedGradientNorm ε f x ≤ v x := by
  have hf2 : MemLp f 2 (potentialMeasure φ) :=
    (memLp_congr_ae hfμ).mpr (Lp.memLp _)
  have hd (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (weightedMassResolvent_coordinateDerivative_of_representative
      (hφ.of_le (by simp)) ht (hg2.toLp g) (hf.of_le (by simp)) hfμ i)).mpr (Lp.memLp _)
  have hLval (x : Space n) : weightedDiffusion φ f x=t⁻¹*(f x-g x) := by
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [heq x]
  have hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ) := by
    rw [show weightedDiffusion φ f = fun x => t⁻¹*(f x-g x) from funext hLval]
    exact (hf2.sub hg2).const_mul _
  obtain ⟨v,hv,hv2,hdv,_,hvμ,_,hev⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht
      (regularizedGradientNorm_contDiff hε hg) (regularizedGradientNorm_memLp hε hg hgrad)
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact ⟨v,hv,hv2,hdv,hvμ,hev,
    regularizedGradientNorm_le_of_resolvent_equations (hφ.of_le (by simp)) hf
      (hg.of_le (by simp)) (hv.of_le (by simp)) ht hε heq hev
      (hessianGradientForm_nonneg_of_convex (hφ.of_le (by simp)) hconv f)
      hL hd (hv2.integrable (by norm_num)) hgv⟩

end KLS
end
