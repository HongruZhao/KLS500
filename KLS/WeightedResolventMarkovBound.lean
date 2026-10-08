import KLS.WeightedResolventPositivity

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual resolvent preserves every real constant. -/
theorem weightedMassResolvent_const_ae
    (hφ : Continuous φ) {t : ℝ} (ht : 0 < t) (M : ℝ) :
    (weightedMassResolvent φ ht (M • CenteredL2.oneLp (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun _ => M := by
  rw [map_smul, weightedMassResolvent_one hφ ht]
  filter_upwards [Lp.coeFn_smul M (CenteredL2.oneLp (potentialMeasure φ)),
    CenteredL2.oneLp_ae (potentialMeasure φ)] with x hx hy
  simp only [hx, Pi.smul_apply, smul_eq_mul, hy, mul_one]

/-- Essential upper bounds of arbitrary L2 forcing pass to its actual resolvent. -/
theorem weightedMassResolvent_upper_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {M : ℝ}
    (hgM : ∀ᵐ x ∂potentialMeasure φ, g x ≤ M) :
    ∀ᵐ x ∂potentialMeasure φ, weightedMassResolvent φ ht g x ≤ M := by
  have hC : (M • CenteredL2.oneLp (potentialMeasure φ) : Lp ℝ 2 (potentialMeasure φ))
      =ᵐ[potentialMeasure φ] fun _ => M := by
    filter_upwards [Lp.coeFn_smul M (CenteredL2.oneLp (potentialMeasure φ)),
      CenteredL2.oneLp_ae (potentialMeasure φ)] with x hx hy
    simp only [hx, Pi.smul_apply, smul_eq_mul, hy, mul_one]
  have hin : ∀ᵐ x ∂potentialMeasure φ,
      g x ≤ (M • CenteredL2.oneLp (potentialMeasure φ)) x := by
    filter_upwards [hgM,hC] with x hx hy
    simpa only [hy] using hx
  have hout := weightedMassResolvent_order hφ ht g
    (M • CenteredL2.oneLp (potentialMeasure φ)) hin
  filter_upwards [hout,weightedMassResolvent_const_ae hφ.continuous ht M] with x hx hy
  simpa only [hy] using hx

/-- Essential lower bounds also pass to arbitrary L2 resolvent values. -/
theorem weightedMassResolvent_lower_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {M : ℝ}
    (hgM : ∀ᵐ x ∂potentialMeasure φ, M ≤ g x) :
    ∀ᵐ x ∂potentialMeasure φ, M ≤ weightedMassResolvent φ ht g x := by
  have hn : ∀ᵐ x ∂potentialMeasure φ, (-g) x ≤ -M := by
    filter_upwards [hgM,Lp.coeFn_neg g] with x hx hy
    simpa only [hy,Pi.neg_apply] using neg_le_neg hx
  have hout := weightedMassResolvent_upper_bound hφ ht (-g) hn
  rw [map_neg] at hout
  filter_upwards [hout,Lp.coeFn_neg (weightedMassResolvent φ ht g)] with x hx hy
  rw [hy] at hx
  exact neg_le_neg_iff.mp hx

/-- The actual mass-preserving resolvent is an essential-supremum contraction
on the bounded part of its whole L2 domain. -/
theorem weightedMassResolvent_abs_bound
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {M : ℝ}
    (hgM : ∀ᵐ x ∂potentialMeasure φ, |g x| ≤ M) :
    ∀ᵐ x ∂potentialMeasure φ, |weightedMassResolvent φ ht g x| ≤ M := by
  have hu := weightedMassResolvent_upper_bound hφ ht g (hgM.mono fun _ hx => (abs_le.mp hx).2)
  have hl := weightedMassResolvent_lower_bound hφ ht g (hgM.mono fun _ hx => (abs_le.mp hx).1)
  filter_upwards [hu,hl] with x hx hy
  exact abs_le.mpr ⟨hy,hx⟩

end KLS
end
