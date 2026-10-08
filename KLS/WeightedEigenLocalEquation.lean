import KLS.WeightedRayleighEquation

/-! The genuine graph weak eigenpair satisfies the ordinary local elliptic equation. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Testing the actual graph eigen-equation with a compact smooth function removes its mean,
since the actual value of every graph element is centered. -/
theorem weighted_eigenpair_compact_test {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {lam : ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
      lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
      ∂potentialMeasure φ) = lam * ∫ x, weightedH1Value φ U x * ψ x ∂potentialMeasure φ := by
  obtain ⟨V, hv, hd⟩ := exists_weightedH1_of_smoothCompact hφ hψ hc
  have hleft : weightedEnergyForm φ U V = ∑ i : Fin n,
      ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x ∂potentialMeasure φ := by
    rw [weightedEnergyForm_eq_sum_integral]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_congr_ae (EventuallyEq.rfl.mul (hd i))
  have huI : Integrable (weightedH1Value φ U) (potentialMeasure φ) :=
    (Lp.memLp _).integrable (by norm_num)
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ hψ.continuous hc
  have hA := (Lp.memLp (weightedH1Value φ U)).integrable_mul hψ2
  have hB := huI.mul_const (∫ y, ψ y ∂potentialMeasure φ)
  have hright : inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) =
      ∫ x, weightedH1Value φ U x * ψ x ∂potentialMeasure φ := by
    rw [L2.real_inner_eq_integral]
    calc
      (∫ x, weightedH1Value φ U x * weightedH1Value φ V x ∂potentialMeasure φ) =
          ∫ x, weightedH1Value φ U x * (ψ x - ∫ y, ψ y ∂potentialMeasure φ)
            ∂potentialMeasure φ := integral_congr_ae (EventuallyEq.rfl.mul hv)
      _ = (∫ x, weightedH1Value φ U x * ψ x ∂potentialMeasure φ) -
          ∫ x, weightedH1Value φ U x * (∫ y, ψ y ∂potentialMeasure φ)
            ∂potentialMeasure φ := by simp_rw [mul_sub]; exact integral_sub hA hB
      _ = _ := by rw [integral_mul_const, weightedH1_integral_eq_zero hφ U]; simp
  simpa only [hleft, hright] using hw V

/-- Actual local weak drift equation of the weighted graph eigenpair. The exponential test
cancels the strictly positive density; no regularity of the eigenfunction is assumed. -/
theorem weighted_eigenpair_unweighted_test {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 3 φ)
    {lam : ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
      lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x) +
      (∑ i : Fin n, ∫ x, coordinateDerivative φ i x * weightedH1Derivative φ i U x * ψ x) =
      lam * ∫ x, weightedH1Value φ U x * ψ x := by
  have heq := weighted_eigenpair_compact_test hφ.continuous hw (hψ.mul hφ.exp) hc.mul_right
  have hcancel (x : Space n) : Real.exp (φ x) * Real.exp (-φ x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hderiv (i : Fin n) (x : Space n) :
      coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x =
        Real.exp (φ x) * (coordinateDerivative ψ i x + coordinateDerivative φ i x * ψ x) := by
    have hh := weightedDerivativeTest_exp_mul (hφ.of_le (by norm_num))
      (hψ.of_le (by norm_num)) i x
    dsimp only [weightedDerivativeTest] at hh
    nlinarith
  have hleft (i : Fin n) :
      (∫ x, weightedH1Derivative φ i U x *
        coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x ∂potentialMeasure φ) =
      (∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x) +
        ∫ x, coordinateDerivative φ i x * weightedH1Derivative φ i U x * ψ x := by
    have hloc := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
      (Lp.memLp (weightedH1Derivative φ i U)) hφ.continuous
    have hA : Integrable (fun x => weightedH1Derivative φ i U x * coordinateDerivative ψ i x)
        volume := by
      simpa only [smul_eq_mul] using hloc.integrable_smul_right_of_hasCompactSupport
        (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
        (hasCompactSupport_coordinateDerivative hc i)
    have hB : Integrable (fun x => coordinateDerivative φ i x *
        weightedH1Derivative φ i U x * ψ x) volume := by
      have hh := hloc.integrable_smul_right_of_hasCompactSupport
        ((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous.mul hψ.continuous)
        hc.mul_left
      convert hh using 1
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    rw [← integral_add hA hB, integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hderiv]
      calc
        _ = (weightedH1Derivative φ i U x * coordinateDerivative ψ i x +
              coordinateDerivative φ i x * weightedH1Derivative φ i U x * ψ x) *
            (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [hcancel, mul_one]
  have hright : (∫ x, weightedH1Value φ U x * (ψ x * Real.exp (φ x))
      ∂potentialMeasure φ) = ∫ x, weightedH1Value φ U x * ψ x := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      calc
        _ = (weightedH1Value φ U x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [hcancel, mul_one]
  simpa only [hleft, hright, Finset.sum_add_distrib] using heq

end KLS
end

#print axioms KLS.weighted_eigenpair_unweighted_test
