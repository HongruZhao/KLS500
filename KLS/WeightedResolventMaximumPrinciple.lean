import KLS.WeightedMassResolventClassicalTest
import KLS.SmoothUpperTest

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ}

/-- Continuity and the everywhere-positive density upgrade an essential bound. -/
theorem continuous_le_const_of_ae_potentialMeasure (hφ : Continuous φ)
    {f : Space n → ℝ} (hf : Continuous f) {M : ℝ}
    (h : ∀ᵐ x ∂potentialMeasure φ, f x ≤ M) : ∀ x, f x ≤ M := by
  have hv : ∀ᵐ x ∂(volume : Measure (Space n)), f x ≤ M :=
    (volume_absolutelyContinuous_potentialMeasure hφ).ae_le h
  have hz : (fun x => max (f x - M) 0) =ᵐ[volume] fun _ => (0 : ℝ) :=
    hv.mono fun _ hx => max_eq_right (sub_nonpos.mpr hx)
  have heq := MeasureTheory.Measure.eq_of_ae_eq hz
    ((hf.sub continuous_const).max continuous_const) continuous_const
  intro x
  have hx := congrFun heq x
  have hle := le_max_left (f x - M) 0
  rw [hx] at hle
  linarith

variable [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual resolvent satisfies the upper maximum principle whenever its
value has a C1 representative. The bounded monotone test and its graph
membership are constructed in the proof. -/
theorem weightedMassResolvent_upper_bound_of_representative
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfμ : f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    {M : ℝ} (hgM : ∀ᵐ x ∂potentialMeasure φ, g x ≤ M) : ∀ x, f x ≤ M := by
  have hf2 : MemLp f 2 (potentialMeasure φ) := (memLp_congr_ae hfμ).mpr (Lp.memLp _)
  have hd (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (weightedMassResolvent_coordinateDerivative_of_representative
      hφ ht g hf hfμ i)).mpr (Lp.memLp _)
  obtain ⟨hψ, heψ⟩ := smoothUpperTest_faithful hf hd M
  have he := weightedMassResolvent_classical_faithful_test hφ ht g hf hfμ hψ heψ
  have hsum : 0 ≤ ∑ i : Fin n, ∫ x,
      coordinateDerivative f i x * coordinateDerivative (smoothUpperTest f M) i x
        ∂potentialMeasure φ := by
    apply Finset.sum_nonneg
    intro i _
    exact integral_nonneg (smoothUpperTest_gradient_pairing_nonneg hf M i)
  have hfψ : Integrable (fun x => f x * smoothUpperTest f M x) (potentialMeasure φ) :=
    hf2.integrable_mul hψ.2
  have hgψ : Integrable (fun x => g x * smoothUpperTest f M x) (potentialMeasure φ) :=
    (Lp.memLp g).integrable_mul hψ.2
  have hI : Integrable (fun x => (f x - g x) * smoothUpperTest f M x)
      (potentialMeasure φ) := by
    simp_rw [sub_mul]
    exact hfψ.sub hgψ
  have hsplit : (∫ x, (f x - g x) * smoothUpperTest f M x ∂potentialMeasure φ) =
      (∫ x, f x * smoothUpperTest f M x ∂potentialMeasure φ) -
        ∫ x, g x * smoothUpperTest f M x ∂potentialMeasure φ := by
    simp_rw [sub_mul]
    exact integral_sub hfψ hgψ
  have hle : (∫ x, (f x - g x) * smoothUpperTest f M x ∂potentialMeasure φ) ≤ 0 := by
    rw [hsplit]
    nlinarith [mul_nonneg ht.le hsum]
  have hnonneg : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ (f x - g x) * smoothUpperTest f M x := by
    filter_upwards [hgM] with x hx
    by_cases hfx : f x ≤ M
    · rw [smoothUpperTest_eq_zero hfx, mul_zero]
    · exact mul_nonneg (sub_nonneg.mpr (hx.trans (le_of_not_ge hfx)))
        (smoothUpperTest_nonneg f M x)
  have hzero : (∫ x, (f x - g x) * smoothUpperTest f M x ∂potentialMeasure φ) = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hnonneg)
  have hzeroAE := (integral_eq_zero_iff_of_nonneg_ae hnonneg hI).mp hzero
  apply continuous_le_const_of_ae_potentialMeasure hφ.continuous hf.continuous
  filter_upwards [hgM, hzeroAE] with x hx hz
  by_contra hn
  have hfx := lt_of_not_ge hn
  have hp : 0 < (f x - g x) * smoothUpperTest f M x :=
    mul_pos (sub_pos.mpr (hx.trans_lt hfx)) (smoothUpperTest_pos hfx)
  change (f x - g x) * smoothUpperTest f M x = 0 at hz
  linarith

/-- The lower maximum principle follows from the proved upper principle
and linearity of the actual mass-preserving resolvent. -/
theorem weightedMassResolvent_lower_bound_of_representative
    (hφ : ContDiff ℝ 1 φ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfμ : f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht g : Space n → ℝ))
    {M : ℝ} (hgM : ∀ᵐ x ∂potentialMeasure φ, M ≤ g x) : ∀ x, M ≤ f x := by
  have hneg : (fun x => -f x) =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (-g) : Space n → ℝ) := by
    rw [map_neg]
    exact hfμ.neg.trans (Lp.coeFn_neg _).symm
  have hbound : ∀ᵐ x ∂potentialMeasure φ, (-g) x ≤ -M := by
    filter_upwards [hgM, Lp.coeFn_neg g] with x hx hy
    simpa only [hy, Pi.neg_apply] using neg_le_neg hx
  have h := weightedMassResolvent_upper_bound_of_representative hφ ht (-g) hf.neg hneg hbound
  intro x
  have hx := h x
  linarith

end KLS
end
