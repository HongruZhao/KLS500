import ResolventEntropyMixedStep
import ResolventUniformLag
import EntropyClock

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

theorem entropy_profile_relative_of_lag {η : ℝ → ℝ} {B m D t L e : ℝ}
    (_hm : 0 < m) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hlow : ∀ r, |r| ≤ B → m ≤ η r)
    (hlip : ∀ r s, |r| ≤ B → |s| ≤ B → |η s-η r| ≤ D*|s-r|)
    (hsmall : D*(t*L) ≤ e*m) {r s : ℝ}
    (hr : |r| ≤ B) (hs : |s| ≤ B) (hlag : |s-r| ≤ t*L) :
    η s ≤ (1+e)*η r := by
  have hd := (le_abs_self (η s-η r)).trans
    ((hlip r s hr hs).trans (mul_le_mul_of_nonneg_left hlag hD))
  have hm' := mul_le_mul_of_nonneg_left (hlow r hr) he
  nlinarith only [hd,hsmall,hm']

/-- Any continuous actual resolvent representative inherits a uniform bound. -/
theorem entropy_resolvent_abs_bound_of_representative
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {g v : Space n → ℝ} (hg2 : MemLp g 2 (potentialMeasure φ))
    (hv : Continuous v)
    (hvμ : v =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ))
    {B : ℝ} (hgB : ∀ x, |g x| ≤ B) : ∀ x, |v x| ≤ B := by
  have hin : ∀ᵐ x ∂potentialMeasure φ, |hg2.toLp g x| ≤ B := by
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx]
    exact hgB x
  have hout := weightedMassResolvent_abs_bound hφ ht (hg2.toLp g) hin
  apply continuous_le_const_of_ae_potentialMeasure hφ.continuous hv.abs
  filter_upwards [hout,hvμ] with x hx hy
  simpa only [hy] using hx

/-- The mixed entropy invariant is proved for actual consecutive resolvent
powers. Smooth representatives, uniform bounds, and every auxiliary domain
condition are constructed rather than assumed for the iterate sequence. -/
theorem weightedMassResolvent_exists_iterated_entropy_pair
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {t B m H D M L e : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hlow : ∀ r, |r| ≤ B → m ≤ η r)
    (hhigh : ∀ r, |r| ≤ B → |η r| ≤ H)
    (hderiv : ∀ r, |r| ≤ B → |deriv η r| ≤ D)
    (hconc : ∀ r s, |r| ≤ B → |s| ≤ B → η s ≤ η r+deriv η r*(s-r))
    (hcurv : ∀ r, |r| ≤ B → 1 ≤ η r*(-deriv (deriv η) r))
    (hlip : ∀ r s, |r| ≤ B → |s| ≤ B → |η s-η r| ≤ D*|s-r|)
    (hsmall : D*(t*L) ≤ e*m)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (hgL : ∀ x, |weightedDiffusion φ g x| ≤ L) (k : ℕ) :
    ∃ u v : Space n → ℝ, ∃ _hu2 : MemLp u 2 (potentialMeasure φ),
      ∃ _hv2 : MemLp v 2 (potentialMeasure φ),
      ContDiff ℝ (⊤ : ℕ∞) u ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      u =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) : Space n → ℝ) ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=u x) ∧
      (∀ x, |u x| ≤ B) ∧ (∀ x, |v x| ≤ B) ∧
      (∀ x, ‖gradient u x‖ ≤ M) ∧ (∀ x, ‖gradient v x‖ ≤ M) ∧
      ∀ x, (Real.sqrt (t/(1+e))*entropyClock k)*‖gradient v x‖ ≤ η (u x) := by
  have hepos : 0 < 1+e := by positivity
  have hs : 0 < t/(1+e) := div_pos ht hepos
  induction k with
  | zero =>
    obtain ⟨v,hv,hv2,_hdv,hvμ,_hm,hev,hvM⟩ :=
      weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hg hg2 hM hgM
    have hvB := entropy_resolvent_abs_bound_of_representative hφ ht hg2 hv.continuous hvμ hgB
    refine ⟨g,v,hg2,hv2,hg,hv,?_,?_,hev,hgB,hvB,hgM,hvM,?_⟩
    · simpa only [Function.iterate_zero,id_eq] using hg2.coeFn_toLp.symm
    · simpa only [zero_add,Function.iterate_one] using hvμ
    · intro x
      simpa only [entropyClock,mul_zero,zero_mul] using hm.le.trans (hlow (g x) (hgB x))
  | succ k ih =>
    obtain ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,huB,hvB,huM,hvM,hbound⟩ := ih
    obtain ⟨z,hz,hz2,_hdz,hzμ,_hm,hez,hzM⟩ :=
      weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hv hv2 hM hvM
    have hzB := entropy_resolvent_abs_bound_of_representative hφ ht hv2 hz.continuous hzμ hvB
    have hvLp : hv2.toLp v = (weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) := by
      apply Lp.ext
      exact hv2.coeFn_toLp.trans hvμ
    have hzμ' : z =ᵐ[potentialMeasure φ]
        ((weightedMassResolvent φ ht)^[k+1+1] (hg2.toLp g) : Space n → ℝ) := by
      rw [hvLp] at hzμ
      simpa only [Function.iterate_succ_apply'] using hzμ
    have hlag := weightedMassResolvent_iterate_lag_of_representatives
      hφ hconv ht hg hg2 hM hgM hgL (k+1) hv.continuous hz.continuous hvμ hzμ'
    have hrelative (x : Space n) : η (z x) ≤ (1+e)*η (v x) :=
      entropy_profile_relative_of_lag hm hD he hlow hlip hsmall (hvB x) (hzB x) (hlag x)
    have ha : 0 ≤ Real.sqrt (t/(1+e))*entropyClock k :=
      mul_nonneg (Real.sqrt_nonneg _) (entropyClock_nonneg k)
    have hab : Real.sqrt (t/(1+e))*entropyClock k ≤
        Real.sqrt (t/(1+e))*entropyClock (k+1) :=
      mul_le_mul_of_nonneg_left (entropyClock_le_succ k) (Real.sqrt_nonneg _)
    have hnew := weightedMassResolvent_entropy_mixed_step hφ hconv hη hu hv hz hv2
      ht hm hD hM ha he hev hez hzμ
      (fun x => hhigh (u x) (huB x)) (fun x => hhigh (v x) (hvB x))
      (fun x => hhigh (z x) (hzB x))
      (fun x => hlow (v x) (hvB x)) (fun x => hlow (z x) (hzB x))
      (fun x => hderiv (v x) (hvB x)) (fun x => hderiv (z x) (hzB x)) hvM hzM
      (fun x => hconc (v x) (u x) (hvB x) (huB x))
      (fun x => hconc (z x) (v x) (hzB x) (hvB x))
      (fun x => hcurv (v x) (hvB x)) (fun x => hcurv (z x) (hzB x))
      hrelative hbound hab (entropyClock_scaled_succ_equation hs.le k)
    exact ⟨v,z,hv2,hz2,hv,hz,hvμ,hzμ',hez,hvB,hzB,hvM,hzM,hnew⟩

/-- Positive clock ranks turn the constructed mixed invariant into a pointwise
gradient estimate for the actual next resolvent iterate. -/
theorem weightedMassResolvent_exists_iterated_entropy_gradient_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {t B m H D M L e : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hlow : ∀ r, |r| ≤ B → m ≤ η r)
    (hhigh : ∀ r, |r| ≤ B → |η r| ≤ H)
    (hderiv : ∀ r, |r| ≤ B → |deriv η r| ≤ D)
    (hconc : ∀ r s, |r| ≤ B → |s| ≤ B → η s ≤ η r+deriv η r*(s-r))
    (hcurv : ∀ r, |r| ≤ B → 1 ≤ η r*(-deriv (deriv η) r))
    (hlip : ∀ r s, |r| ≤ B → |s| ≤ B → |η s-η r| ≤ D*|s-r|)
    (hsmall : D*(t*L) ≤ e*m)
    {g : Space n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (hgL : ∀ x, |weightedDiffusion φ g x| ≤ L) (k : ℕ) (hk : 1 ≤ k) :
    ∃ u v : Space n → ℝ, ∃ _hu2 : MemLp u 2 (potentialMeasure φ),
      ∃ _hv2 : MemLp v 2 (potentialMeasure φ),
      ContDiff ℝ (⊤ : ℕ∞) u ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      u =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k] (hg2.toLp g) : Space n → ℝ) ∧
      v =ᵐ[potentialMeasure φ] ((weightedMassResolvent φ ht)^[k+1] (hg2.toLp g) : Space n → ℝ) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=u x) ∧
      (∀ x, |u x| ≤ B) ∧ (∀ x, |v x| ≤ B) ∧
      (∀ x, ‖gradient u x‖ ≤ M) ∧ (∀ x, ‖gradient v x‖ ≤ M) ∧
      ∀ x, ‖gradient v x‖ ≤ H/(Real.sqrt (t/(1+e))*entropyClock k) := by
  obtain ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,huB,hvB,huM,hvM,hbound⟩ :=
    weightedMassResolvent_exists_iterated_entropy_pair hφ hconv hη ht hm hD hM he
      hlow hhigh hderiv hconc hcurv hlip hsmall hg hg2 hgB hgM hgL k
  refine ⟨u,v,hu2,hv2,hu,hv,huμ,hvμ,hev,huB,hvB,huM,hvM,?_⟩
  intro x
  have hclock : 0 < Real.sqrt (t/(1+e))*entropyClock k :=
    mul_pos (Real.sqrt_pos.mpr (div_pos ht (by positivity))) (entropyClock_pos hk)
  apply (le_div_iff₀ hclock).mpr
  have hh := (hbound x).trans ((le_abs_self (η (u x))).trans (hhigh (u x) (huB x)))
  simpa only [mul_comm] using hh

end KLS.ConstantReduction
end
