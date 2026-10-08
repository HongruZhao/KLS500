import ResolventGradientDomination
import ResolventWeightedCauchy

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Weighted gradient domination for genuine resolvents, with arbitrary L2
weights. A positive lower bound on the first input permits removal of the
Kato regularization without constructing a resolver of the nonsmooth norm. -/
theorem weightedMassResolvent_gradient_weighted_domination
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {f g p q P Q : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgrad : MemLp (gradient g) 2 (potentialMeasure φ))
    (hfμ : f =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ))
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hp2 : MemLp p 2 (potentialMeasure φ)) (hq2 : MemLp q 2 (potentialMeasure φ))
    (hP : Continuous P) (hQ : Continuous Q)
    (hPμ : P =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hp2.toLp p) : Space n → ℝ))
    (hQμ : Q =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hq2.toLp q) : Space n → ℝ))
    {m : ℝ} (hm : 0 < m) (hpm : ∀ x, m ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hdom : ∀ x, ‖gradient g x‖^2 ≤ p x*q x) :
    ∀ x, ‖gradient f x‖^2 ≤ P x*Q x := by
  have hPm : ∀ x, m ≤ P x := by
    have hin : ∀ᵐ x ∂potentialMeasure φ, m ≤ hp2.toLp p x := by
      filter_upwards [hp2.coeFn_toLp] with x hx
      rw [hx]
      exact hpm x
    have hout := weightedMassResolvent_lower_bound hφ ht (hp2.toLp p) hin
    have hae : ∀ᵐ x ∂potentialMeasure φ, -P x ≤ -m := by
      filter_upwards [hout,hPμ] with x hx hy
      rw [←hy] at hx
      linarith
    have hh := continuous_le_const_of_ae_potentialMeasure hφ.continuous hP.neg hae
    intro x
    have hhx := hh x
    change -P x ≤ -m at hhx
    linarith
  have heps (ε : ℝ) (hε : 0 < ε) (x : Space n) :
      ‖gradient f x‖^2 ≤ P x*(Q x+ε^2/m) := by
    obtain ⟨v,hv,_hv2,_hdv,hvμ,_hev,hvf⟩ :=
      weightedMassResolvent_regularized_gradient_subcommutation hφ hconv ht hε
        hf hg hg2 hgrad hfμ heq
    let A : Lp ℝ 2 (potentialMeasure φ) := hp2.toLp p
    let B : Lp ℝ 2 (potentialMeasure φ) :=
      hq2.toLp q+(ε^2/m) • CenteredL2.oneLp (potentialMeasure φ)
    let G : Lp ℝ 2 (potentialMeasure φ) :=
      (regularizedGradientNorm_memLp hε hg hgrad).toLp (regularizedGradientNorm ε g)
    have hAμ : (A : Space n → ℝ) =ᵐ[potentialMeasure φ] p := hp2.coeFn_toLp
    have hBμ : (B : Space n → ℝ) =ᵐ[potentialMeasure φ] fun y => q y+ε^2/m := by
      filter_upwards [Lp.coeFn_add (hq2.toLp q) ((ε^2/m) • CenteredL2.oneLp (potentialMeasure φ)),
        Lp.coeFn_smul (ε^2/m) (CenteredL2.oneLp (potentialMeasure φ)),
        CenteredL2.oneLp_ae (potentialMeasure φ),hq2.coeFn_toLp] with y hadd hsmul hone hqy
      dsimp only [B]
      rw [hadd,Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul,hone,mul_one,hqy]
    have hGμ : (G : Space n → ℝ) =ᵐ[potentialMeasure φ] regularizedGradientNorm ε g :=
      (regularizedGradientNorm_memLp hε hg hgrad).coeFn_toLp
    have hA0 : ∀ᵐ y ∂potentialMeasure φ, 0 ≤ A y := by
      filter_upwards [hAμ] with y hy
      rw [hy]
      exact hm.le.trans (hpm y)
    have hB0 : ∀ᵐ y ∂potentialMeasure φ, 0 ≤ B y := by
      filter_upwards [hBμ] with y hy
      rw [hy]
      exact add_nonneg (hq y) (div_nonneg (sq_nonneg _) hm.le)
    have hAB : ∀ᵐ y ∂potentialMeasure φ, (G y)^2 ≤ A y*B y := by
      filter_upwards [hAμ,hBμ,hGμ] with y hAy hBy hGy
      rw [hAy,hBy,hGy,regularizedGradientNorm_sq]
      have hcor : ε^2 ≤ p y*(ε^2/m) := by
        have hh := mul_le_mul_of_nonneg_right (hpm y) (div_nonneg (sq_nonneg ε) hm.le)
        have he : m*(ε^2/m)=ε^2 := by field_simp
        rw [he] at hh
        exact hh
      nlinarith [hdom y]
    have hBout : (fun y => Q y+ε^2/m) =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht B : Space n → ℝ) := by
      have hb : weightedMassResolvent φ ht B=
          weightedMassResolvent φ ht (hq2.toLp q)+
            weightedMassResolvent φ ht ((ε^2/m) • CenteredL2.oneLp (potentialMeasure φ)) := by
        dsimp only [B]
        exact map_add _ _ _
      rw [hb]
      filter_upwards [hQμ,weightedMassResolvent_const_ae hφ.continuous ht (ε^2/m),
        Lp.coeFn_add (weightedMassResolvent φ ht (hq2.toLp q))
          (weightedMassResolvent φ ht ((ε^2/m) • CenteredL2.oneLp (potentialMeasure φ)))]
        with y hQy hcy hadd
      rw [hadd,Pi.add_apply,←hQy,hcy]
    have hcs := ConstantReduction.weightedMassResolvent_weighted_cauchy_of_representatives
      hφ ht A B G hA0 hB0 hAB hP (hQ.add continuous_const) hv.continuous hPμ hBout hvμ x
    change v x^2 ≤ P x*(Q x+ε^2/m) at hcs
    have hfv := (norm_gradient_le_regularizedGradientNorm ε f x).trans (hvf x)
    have hv0 := (norm_nonneg (gradient f x)).trans hfv
    nlinarith [norm_nonneg (gradient f x)]
  intro x
  have hP0 : 0 ≤ P x := hm.le.trans (hPm x)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hP1 : 0 < P x+1 := by linarith
  let ε := Real.sqrt (δ*m/(P x+1))
  have hε : 0 < ε := by dsimp [ε];positivity
  have hsε : ε^2=δ*m/(P x+1) := Real.sq_sqrt (by positivity)
  have hsmall : P x*(ε^2/m) ≤ δ := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hm).mpr
    rw [hsε,←mul_div_assoc]
    apply (div_le_iff₀ hP1).mpr
    nlinarith
  have hh := heps ε hε x
  nlinarith

end KLS
end
