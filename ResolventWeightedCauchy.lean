import KLS.WeightedResolventPositivity
import Mathlib.Algebra.QuadraticDiscriminant

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem quadratic_nonneg_of_weighted_square {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : w^2 ≤ u*v) (r : ℝ) :
    0 ≤ u*r^2-2*w*r+v := by
  rcases hu.eq_or_lt with hu | hu
  · have hw0 : w = 0 := by rw [← hu] at hw; nlinarith only [hw, sq_nonneg w]
    rw [← hu, hw0]
    simpa using hv
  · apply (mul_nonneg_iff_of_pos_left hu).mp
    nlinarith only [hw, sq_nonneg (u*r-w)]

/-- Weighted Cauchy--Schwarz for the actual positive mass resolvent on its
full L2 domain. Rational quadratic tests allow one common almost-everywhere
set before taking the discriminant. -/
theorem weightedMassResolvent_weighted_cauchy
    {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (u v w : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ u x)
    (hv : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ v x)
    (hw : ∀ᵐ x ∂potentialMeasure φ, (w x)^2 ≤ u x*v x) :
    ∀ᵐ x ∂potentialMeasure φ,
      (weightedMassResolvent φ ht w x)^2 ≤
        weightedMassResolvent φ ht u x*weightedMassResolvent φ ht v x := by
  let R := weightedMassResolvent φ ht
  have hq (q : ℚ) : ∀ᵐ x ∂potentialMeasure φ,
      0 ≤ R u x*(q : ℝ)^2-2*R w x*(q : ℝ)+R v x := by
    let g : Lp ℝ 2 (potentialMeasure φ) :=
      (q : ℝ)^2 • u + (-2*(q : ℝ)) • w + v
    have hg : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ g x := by
      filter_upwards [hu,hv,hw,Lp.coeFn_add ((q : ℝ)^2 • u) ((-2*(q : ℝ)) • w),
        Lp.coeFn_add ((q : ℝ)^2 • u + (-2*(q : ℝ)) • w) v,
        Lp.coeFn_smul ((q : ℝ)^2) u,Lp.coeFn_smul (-2*(q : ℝ)) w]
        with x hux hvx hwx hadd hadd' hsmul hsmul'
      change 0 ≤ ((q : ℝ)^2 • u + (-2*(q : ℝ)) • w + v) x
      rw [hadd',Pi.add_apply,hadd,Pi.add_apply,hsmul,hsmul',Pi.smul_apply,Pi.smul_apply]
      simpa only [smul_eq_mul] using
        (show 0 ≤ (q : ℝ)^2*u x+(-2*(q : ℝ))*w x+v x by
          nlinarith only [quadratic_nonneg_of_weighted_square hux hvx hwx (q : ℝ)])
    have hp := weightedMassResolvent_nonneg hφ ht g hg
    have hmap : R g = (q : ℝ)^2 • R u + (-2*(q : ℝ)) • R w + R v := by
      dsimp only [g,R]
      simp only [map_add,map_smul]
    rw [hmap] at hp
    filter_upwards [hp,Lp.coeFn_add ((q : ℝ)^2 • R u) ((-2*(q : ℝ)) • R w),
      Lp.coeFn_add ((q : ℝ)^2 • R u + (-2*(q : ℝ)) • R w) (R v),
      Lp.coeFn_smul ((q : ℝ)^2) (R u),Lp.coeFn_smul (-2*(q : ℝ)) (R w)]
      with x hx hadd hadd' hsmul hsmul'
    rw [hadd',Pi.add_apply,hadd,Pi.add_apply,hsmul,hsmul',Pi.smul_apply,Pi.smul_apply] at hx
    dsimp only [smul_eq_mul] at hx
    nlinarith only [hx]
  have hqa : ∀ᵐ x ∂potentialMeasure φ, ∀ q : ℚ,
      0 ≤ R u x*(q : ℝ)^2-2*R w x*(q : ℝ)+R v x := ae_all_iff.mpr hq
  filter_upwards [hqa] with x hx
  have hr (r : ℝ) : 0 ≤ R u x*r^2-2*R w x*r+R v x := by
    refine Rat.denseRange_cast.induction_on r ?_ hx
    exact isClosed_le continuous_const (by fun_prop)
  have hd := discrim_le_zero (a := R u x) (b := -2*R w x) (c := R v x)
    (fun r => by nlinarith only [hr r])
  dsimp only [discrim] at hd
  change (R w x)^2 ≤ R u x*R v x
  nlinarith only [hd]

/-- Continuous representatives of the three genuine resolvents satisfy the
same weighted inequality at every point. -/
theorem weightedMassResolvent_weighted_cauchy_of_representatives
    {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (u v w : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ u x)
    (hv : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ v x)
    (hw : ∀ᵐ x ∂potentialMeasure φ, (w x)^2 ≤ u x*v x)
    {U V W : Space n → ℝ} (hU : Continuous U) (hV : Continuous V) (hW : Continuous W)
    (hUa : U =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht u : Space n → ℝ))
    (hVa : V =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht v : Space n → ℝ))
    (hWa : W =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht w : Space n → ℝ)) :
    ∀ x, (W x)^2 ≤ U x*V x := by
  have h := weightedMassResolvent_weighted_cauchy hφ ht u v w hu hv hw
  have hae : ∀ᵐ x ∂potentialMeasure φ, (W x)^2-U x*V x ≤ 0 := by
    filter_upwards [h,hUa,hVa,hWa] with x hx hux hvx hwx
    rw [← hux,← hvx,← hwx] at hx
    exact sub_nonpos.mpr hx
  have hpoint := continuous_le_const_of_ae_potentialMeasure hφ.continuous
    ((hW.pow 2).sub (hU.mul hV)) hae
  intro x
  exact sub_nonpos.mp (hpoint x)

end KLS.ConstantReduction
end
