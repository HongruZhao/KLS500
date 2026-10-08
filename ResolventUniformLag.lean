import KLS.WeightedResolventGradientContraction
import KLS.WeightedSubsolutionMaximum
import KLS.WeightedResolventMarkovBound
import KLS.ActualGradientIntegrability
import KLS.WeakWeightedIntegration

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

omit [IsProbabilityMeasure (potentialMeasure φ)] in
theorem lag_weightedDiffusion_const (c : ℝ) (x : Space n) :
    weightedDiffusion φ (fun _ : Space n => c) x = 0 := by
  have hdconst (i : Fin n) : coordinateDerivative (fun _ : Space n => c) i = 0 := by
    funext y
    simp [coordinateDerivative]
  simp [weightedDiffusion_eq_sum,coordinateHessian,hdconst,coordinateDerivative]

/-- The global subsolution principle permits comparison with any constant
when the actual value and gradient have their ordinary integrability. -/
theorem le_const_of_weighted_resolvent_subsolution
    (hφ : ContDiff ℝ 2 φ) {u : Space n → ℝ} (hu : ContDiff ℝ 3 u)
    {t D : ℝ} (ht : 0<t) (hsub : ∀ x,u x-t*weightedDiffusion φ u x≤D)
    (huI : Integrable u (potentialMeasure φ))
    (hguI : Integrable (gradient u) (potentialMeasure φ)) : ∀ x,u x≤D := by
  let w : Space n → ℝ := u+fun _ => -D
  have hw : ContDiff ℝ 3 w := hu.add contDiff_const
  have hIw : Integrable w (potentialMeasure φ) := huI.add (integrable_const (-D))
  have hgw : gradient w=gradient u := by
    funext x
    dsimp only [w]
    rw [gradient_add_real (hu.differentiable (by norm_num) x) (differentiableAt_const (-D))]
    simp
  have hsw (x : Space n) : w x-t*weightedDiffusion φ w x≤0 := by
    have hL : weightedDiffusion φ w x=weightedDiffusion φ u x := by
      dsimp only [w]
      rw [weightedDiffusion_add (hu.of_le (by norm_num)) contDiff_const,
        lag_weightedDiffusion_const,add_zero]
    rw [hL]
    dsimp only [w,Pi.add_apply]
    linarith [hsub x]
  have hgIw : Integrable (gradient w) (potentialMeasure φ) := by rw [hgw];exact hguI
  have hh := nonpos_of_weighted_resolvent_subsolution hφ hw ht hsw hIw hgIw.norm
  intro x
  have hx := hh x
  change u x+(-D)≤0 at hx
  linarith

/-- Classical resolvent equations are contractions in the uniform norm.
The proof uses the already constructed global elliptic maximum principle. -/
theorem abs_sub_le_of_weighted_resolvent_equations
    (hφ : ContDiff ℝ 2 φ) {u v f g : Space n → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {t D : ℝ} (ht : 0<t)
    (heu : ∀ x,u x-t*weightedDiffusion φ u x=f x)
    (hev : ∀ x,v x-t*weightedDiffusion φ v x=g x)
    (huI : Integrable u (potentialMeasure φ)) (hvI : Integrable v (potentialMeasure φ))
    (hguI : Integrable (gradient u) (potentialMeasure φ))
    (hgvI : Integrable (gradient v) (potentialMeasure φ))
    (hfg : ∀ x,|f x-g x|≤D) : ∀ x,|u x-v x|≤D := by
  have hup {a b p q : Space n → ℝ} (ha : ContDiff ℝ 3 a) (hb : ContDiff ℝ 3 b)
      (hea : ∀ x,a x-t*weightedDiffusion φ a x=p x)
      (heb : ∀ x,b x-t*weightedDiffusion φ b x=q x)
      (haI : Integrable a (potentialMeasure φ)) (hbI : Integrable b (potentialMeasure φ))
      (hgaI : Integrable (gradient a) (potentialMeasure φ))
      (hgbI : Integrable (gradient b) (potentialMeasure φ))
      (hpq : ∀ x,p x-q x≤D) : ∀ x,a x-b x≤D := by
    let w : Space n → ℝ := a+(-1 : ℝ) • b
    have hw : ContDiff ℝ 3 w := ha.add (hb.const_smul (-1 : ℝ))
    have hwI : Integrable w (potentialMeasure φ) := haI.add (hbI.smul (-1 : ℝ))
    have hgw : gradient w=gradient a+(-1 : ℝ) • gradient b := by
      funext x
      dsimp only [w]
      rw [gradient_add_real (ha.differentiable (by norm_num) x)
        ((hb.differentiable (by norm_num) x).const_smul (-1 : ℝ)),
        gradient_smul_real (hb.differentiable (by norm_num) x)]
      rfl
    have hgwI : Integrable (gradient w) (potentialMeasure φ) := by
      rw [hgw]
      exact hgaI.add (hgbI.smul (-1 : ℝ))
    have hsub (x : Space n) : w x-t*weightedDiffusion φ w x≤D := by
      have hL : weightedDiffusion φ w x=weightedDiffusion φ a x+(-1 : ℝ)*weightedDiffusion φ b x := by
        dsimp only [w]
        rw [weightedDiffusion_add (f:=a) (g:=(-1 : ℝ) • b) (ha.of_le (by norm_num))
          ((hb.const_smul (-1 : ℝ)).of_le (by norm_num)),
          weightedDiffusion_smul (hb.of_le (by norm_num))]
      rw [hL]
      dsimp only [w,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      linarith [hea x,heb x,hpq x]
    have hh := le_const_of_weighted_resolvent_subsolution hφ hw ht hsub hwI hgwI
    intro x
    simpa only [w,Pi.add_apply,Pi.smul_apply,smul_eq_mul,neg_one_mul,sub_eq_add_neg] using hh x
  have hab := hup hu hv heu hev huI hvI hguI hgvI (fun x => (abs_le.mp (hfg x)).2)
  have hba := hup hv hu hev heu hvI huI hgvI hguI (fun x => by linarith [(abs_le.mp (hfg x)).1])
  intro x
  exact abs_le.mpr ⟨by linarith [hba x],hab x⟩

/-- One actual resolvent step changes a smooth function by at most the
time step times its bounded diffusion. -/
theorem weightedMassResolvent_initial_lag_ae
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0<t) {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {M D : ℝ} (hM : 0≤M) (hfM : ∀ x,‖gradient f x‖≤M)
    (hLf : ∀ x,|weightedDiffusion φ f x|≤D) :
    ∀ᵐ x ∂potentialMeasure φ,
      |weightedMassResolvent φ ht (hf2.toLp f) x-(hf2.toLp f) x|≤t*D := by
  obtain ⟨v,hv,hv2,_hdv,hvμ,_hm,hev,hvM⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hf hf2 hM hfM
  have hgf2 : MemLp (gradient f) 2 (potentialMeasure φ) :=
    MemLp.of_bound (continuous_gradient_of_contDiff (hf.of_le (by simp))).aestronglyMeasurable M
      (Eventually.of_forall hfM)
  have hgv2 : MemLp (gradient v) 2 (potentialMeasure φ) :=
    MemLp.of_bound (continuous_gradient_of_contDiff (hv.of_le (by simp))).aestronglyMeasurable M
      (Eventually.of_forall hvM)
  have hinput (x : Space n) : |f x-(f x-t*weightedDiffusion φ f x)|≤t*D := by
    rw [show f x-(f x-t*weightedDiffusion φ f x)=t*weightedDiffusion φ f x by ring,
      abs_mul,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hLf x) ht.le
  have hh := abs_sub_le_of_weighted_resolvent_equations (hφ.of_le (by simp))
    (hv.of_le (by simp)) (hf.of_le (by simp)) ht hev (fun _ => rfl)
    (hv2.integrable (by norm_num)) (hf2.integrable (by norm_num))
    (hgv2.integrable (by norm_num)) (hgf2.integrable (by norm_num)) hinput
  filter_upwards [hvμ,hf2.coeFn_toLp] with x hvx hfx
  rw [←hvx,hfx]
  exact hh x

/-- Uniform lag persists through every power of the actual resolvent,
by its proved order contraction and exact linearity. -/
theorem weightedMassResolvent_iterate_lag_ae
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0<t) {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {M D : ℝ} (hM : 0≤M) (hfM : ∀ x,‖gradient f x‖≤M)
    (hLf : ∀ x,|weightedDiffusion φ f x|≤D) (k : ℕ) :
    ∀ᵐ x ∂potentialMeasure φ,
      |((weightedMassResolvent φ ht)^[k+1] (hf2.toLp f)) x-
        ((weightedMassResolvent φ ht)^[k] (hf2.toLp f)) x|≤t*D := by
  induction k with
  | zero =>
    simpa only [Nat.zero_add,Function.iterate_zero,Function.iterate_one,id_eq] using
      weightedMassResolvent_initial_lag_ae hφ hconv ht hf hf2 hM hfM hLf
  | succ k ih =>
    let a := (weightedMassResolvent φ ht)^[k+1] (hf2.toLp f)
    let b := (weightedMassResolvent φ ht)^[k] (hf2.toLp f)
    have hab : ∀ᵐ x ∂potentialMeasure φ,|(a-b) x|≤t*D := by
      filter_upwards [ih,Lp.coeFn_sub a b] with x hx hy
      simpa only [hy,Pi.sub_apply] using hx
    have hh := weightedMassResolvent_abs_bound hφ ht (a-b) hab
    rw [map_sub] at hh
    filter_upwards [hh,Lp.coeFn_sub (weightedMassResolvent φ ht a)
      (weightedMassResolvent φ ht b)] with x hx hy
    rw [hy] at hx
    simpa only [a,b,Function.iterate_succ_apply',Pi.sub_apply] using hx

/-- Any continuous representatives of consecutive actual iterates inherit
the same pointwise lag bound; no choice of representatives is assumed. -/
theorem weightedMassResolvent_iterate_lag_of_representatives
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0<t) {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {M D : ℝ} (hM : 0≤M) (hfM : ∀ x,‖gradient f x‖≤M)
    (hLf : ∀ x,|weightedDiffusion φ f x|≤D) (k : ℕ)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (huμ : u=ᵐ[potentialMeasure φ]
      ((weightedMassResolvent φ ht)^[k] (hf2.toLp f) : Space n → ℝ))
    (hvμ : v=ᵐ[potentialMeasure φ]
      ((weightedMassResolvent φ ht)^[k+1] (hf2.toLp f) : Space n → ℝ)) :
    ∀ x,|v x-u x|≤t*D := by
  apply continuous_le_const_of_ae_potentialMeasure hφ.continuous ((hv.sub hu).abs)
  have hh := weightedMassResolvent_iterate_lag_ae hφ hconv ht hf hf2 hM hfM hLf k
  filter_upwards [hh,huμ,hvμ] with x hx hux hvx
  simpa only [Pi.sub_apply,hux,hvx] using hx

omit [IsProbabilityMeasure (potentialMeasure φ)] in
/-- Compact smooth initial data automatically supplies finite uniform
gradient and diffusion bounds for the lag theorem. -/
theorem smoothCompact_exists_gradient_diffusion_bounds
    (hφ : ContDiff ℝ 1 φ) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ M D : ℝ,0≤M ∧ 0<D ∧ (∀ x,‖gradient f x‖≤M) ∧
      ∀ x,|weightedDiffusion φ f x|≤D := by
  obtain ⟨M,hM⟩ := (hasCompactSupport_gradient hfc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff (hf.of_le (by norm_num)))
  obtain ⟨D,hD⟩ := (hasCompactSupport_weightedDiffusion_raw hfc).exists_bound_of_continuous
    (continuous_weightedDiffusion_C1 hφ hf)
  have hM0 : 0≤M := (norm_nonneg (gradient f 0)).trans (hM 0)
  have hD0 : 0≤D := (norm_nonneg (weightedDiffusion φ f 0)).trans (hD 0)
  refine ⟨M,D+1,hM0,by linarith,hM,?_⟩
  intro x
  have hh := hD x
  rw [Real.norm_eq_abs] at hh
  linarith

end KLS.ConstantReduction
end
