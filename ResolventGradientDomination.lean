import ResolventGradientL1Subcommutation
import KLS.WeightedResolventMarkovBound

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma norm_gradient_le_regularizedGradientNorm (ε : ℝ) (f : Space n → ℝ) (x : Space n) :
    ‖gradient f x‖ ≤ regularizedGradientNorm ε f x := by
  have hs := regularizedGradientNorm_sq ε f x
  have hr : 0 ≤ regularizedGradientNorm ε f x := Real.sqrt_nonneg _
  nlinarith [sq_nonneg ε,norm_nonneg (gradient f x)]

variable {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- A pointwise linear gradient domination passes through the genuine mass
resolvent. The regularization is removed in the conclusion. -/
theorem weightedMassResolvent_gradient_domination
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {f g p P : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgrad : MemLp (gradient g) 2 (potentialMeasure φ))
    (hfμ : f =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ))
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hp2 : MemLp p 2 (potentialMeasure φ)) (hP : Continuous P)
    (hPμ : P =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hp2.toLp p) : Space n → ℝ))
    {a : ℝ} (ha : 0 ≤ a) (hdom : ∀ x, a*‖gradient g x‖ ≤ p x) :
    ∀ x, a*‖gradient f x‖ ≤ P x := by
  have heps (ε : ℝ) (hε : 0 < ε) (x : Space n) :
      a*‖gradient f x‖ ≤ P x+a*ε := by
    obtain ⟨v,hv,_hv2,_hdv,hvμ,_hev,hvf⟩ :=
      weightedMassResolvent_regularized_gradient_subcommutation hφ hconv ht hε
        hf hg hg2 hgrad hfμ heq
    let G : Lp ℝ 2 (potentialMeasure φ) :=
      (regularizedGradientNorm_memLp hε hg hgrad).toLp (regularizedGradientNorm ε g)
    let H : Lp ℝ 2 (potentialMeasure φ) := hp2.toLp p
    have hGμ : (G : Space n → ℝ) =ᵐ[potentialMeasure φ] regularizedGradientNorm ε g :=
      (regularizedGradientNorm_memLp hε hg hgrad).coeFn_toLp
    have hin : ∀ᵐ y ∂potentialMeasure φ, (a • G-H) y ≤ a*ε := by
      filter_upwards [Lp.coeFn_sub (a • G) H,Lp.coeFn_smul a G,hGμ,hp2.coeFn_toLp]
        with y hsub hsmul hgy hpy
      rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,smul_eq_mul,hgy]
      change a*regularizedGradientNorm ε g y-H y ≤ a*ε
      have hp : H y=p y := hpy
      rw [hp]
      have hh := mul_le_mul_of_nonneg_left (regularizedGradientNorm_le hε.le g y) ha
      linarith [hdom y]
    have hout := weightedMassResolvent_upper_bound hφ ht (a • G-H) hin
    rw [map_sub,map_smul] at hout
    have hae : ∀ᵐ y ∂potentialMeasure φ, a*v y-P y ≤ a*ε := by
      filter_upwards [hout,Lp.coeFn_sub (a • weightedMassResolvent φ ht G)
        (weightedMassResolvent φ ht H),Lp.coeFn_smul a (weightedMassResolvent φ ht G),
        hvμ,hPμ] with y hy hsub hsmul hvy hPy
      rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,smul_eq_mul] at hy
      change a*weightedMassResolvent φ ht G y-weightedMassResolvent φ ht H y ≤ a*ε at hy
      change v y=weightedMassResolvent φ ht G y at hvy
      change P y=weightedMassResolvent φ ht H y at hPy
      rw [←hvy,←hPy] at hy
      exact hy
    have hpoint := continuous_le_const_of_ae_potentialMeasure hφ.continuous
      ((hv.continuous.const_mul a).sub hP) hae x
    change a*v x-P x ≤ a*ε at hpoint
    have hnorm := mul_le_mul_of_nonneg_left
      ((norm_gradient_le_regularizedGradientNorm ε f x).trans (hvf x)) ha
    linarith
  intro x
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hap : 0 < a+1 := by linarith
  have hε : 0 < δ/(a+1) := div_pos hδ hap
  have hh := heps (δ/(a+1)) hε x
  have hsmall : a*(δ/(a+1)) ≤ δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hap).mpr
    nlinarith
  linarith

end KLS
end
