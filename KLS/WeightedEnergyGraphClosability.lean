import KLS.WeightedEnergyGraph
import KLS.WeightedLocalSobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Faithfulness and actual local weak derivatives of the weighted energy graph

The weighted integration identity identifies every derivative coordinate as
an ordinary distributional derivative of the value. Smooth test separation
therefore proves that the value determines the whole graph element. Compact
localization supplies actual Lebesgue L² derivatives with the product formula.
No probability normalization or spectral-gap hypothesis is imposed.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

lemma weightedDerivativeTest_exp_mul {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (i : Fin n) (x : Space n) :
    weightedDerivativeTest φ (fun y => ψ y * Real.exp (φ y)) i x =
      Real.exp (φ x) * coordinateDerivative ψ i x := by
  have hφd := hφ.differentiable (by norm_num) x
  have hψd := hψ.differentiable (by norm_num) x
  have he : coordinateDerivative (fun y => Real.exp (φ y)) i x =
      Real.exp (φ x) * coordinateDerivative φ i x := by
    unfold coordinateDerivative
    have hd := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      hφd.hasFDerivAt.exp.fderiv
    simpa only [smul_apply, smul_eq_mul] using hd
  dsimp only [weightedDerivativeTest]
  rw [coordinateDerivative_mul hψd hφd.exp, he]
  ring

/-- The graph coordinates satisfy the ordinary distributional derivative identity. -/
theorem weightedH1_unweighted_weak_identity {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, weightedH1Value φ U x * coordinateDerivative ψ i x) =
      -(∫ x, weightedH1Derivative φ i U x * ψ x) := by
  have hw := weightedCenteredGradientGraph_weak_identity hφ U (hψ.mul hφ.exp) hc.mul_right i
  rw [integral_potentialMeasure hφ.continuous.measurable,
    integral_potentialMeasure hφ.continuous.measurable] at hw
  have hl : (∫ x, weightedH1Derivative φ i U x * (ψ x * Real.exp (φ x)) *
      Real.exp (-φ x)) = ∫ x, weightedH1Derivative φ i U x * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      calc
        _ = (weightedH1Derivative φ i U x * ψ x) *
          (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hr : (∫ x, weightedH1Value φ U x *
      weightedDerivativeTest φ (fun y => ψ y * Real.exp (φ y)) i x * Real.exp (-φ x)) =
      ∫ x, weightedH1Value φ U x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [weightedDerivativeTest_exp_mul hφ hψ]
      calc
        _ = (weightedH1Value φ U x * coordinateDerivative ψ i x) *
          (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hl, hr] at hw
  linarith

/-- Vanishing of the actual L² value forces every actual derivative coordinate to vanish. -/
theorem weightedH1Derivative_eq_zero_of_value_eq_zero {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {U : WeightedCenteredH1 φ}
    (hU : weightedH1Value φ U = 0) (i : Fin n) : weightedH1Derivative φ i U = 0 := by
  have hv : (weightedH1Value φ U : Space n → ℝ) =ᵐ[volume] fun _ => 0 := by
    apply (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
    rw [hU]
    exact Lp.coeFn_zero ℝ 2 (potentialMeasure φ)
  have hd : (weightedH1Derivative φ i U : Space n → ℝ) =ᵐ[volume] fun _ => 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
        (Lp.memLp (weightedH1Derivative φ i U)) hφ.continuous)
    intro ψ hψ hc
    have hi := weightedH1_unweighted_weak_identity hφ U
      (hψ.of_le (by simp)) hc i
    have hz : (∫ x, weightedH1Value φ U x * coordinateDerivative ψ i x) = 0 := by
      calc
        _ = ∫ x, (0 : ℝ) * coordinateDerivative ψ i x :=
          integral_congr_ae (hv.fun_mul EventuallyEq.rfl)
        _ = 0 := by simp
    rw [hz] at hi
    simpa only [smul_eq_mul, mul_comm] using (neg_eq_zero.mp hi.symm)
  have hac : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  apply Lp.ext
  filter_upwards [hac.ae_eq hd, Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hz
  exact hx.trans hz.symm

/-- The closed gradient graph is faithful: its value projection has trivial kernel. -/
theorem weightedH1_eq_zero_of_value_eq_zero {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {U : WeightedCenteredH1 φ}
    (hU : weightedH1Value φ U = 0) : U = 0 := by
  have he := weightedH1_norm_sq φ U
  have hd := weightedH1Derivative_eq_zero_of_value_eq_zero hφ hU
  simp only [hU, hd, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, add_zero] at he
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg U])

/-- Equality of actual weighted L² values determines equality of graph elements. -/
theorem weightedH1Value_injective {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Function.Injective (weightedH1Value φ) := by
  intro U V huv
  apply sub_eq_zero.mp
  apply weightedH1_eq_zero_of_value_eq_zero hφ
  rw [map_sub, huv, sub_self]


/-- The actual value of a graph element is locally Lebesgue L². -/
theorem weightedH1Value_memLp_restrict {φ : Space n → ℝ}
    (hφ : Continuous φ) (U : WeightedCenteredH1 φ)
    {K : Set (Space n)} (hK : IsCompact K) :
    MemLp (weightedH1Value φ U) 2 (volume.restrict K) :=
  KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp _) hφ hK

/-- Every actual derivative coordinate of a graph element is locally Lebesgue L². -/
theorem weightedH1Derivative_memLp_restrict {φ : Space n → ℝ}
    (hφ : Continuous φ) (U : WeightedCenteredH1 φ) (i : Fin n)
    {K : Set (Space n)} (hK : IsCompact K) :
    MemLp (weightedH1Derivative φ i U) 2 (volume.restrict K) :=
  KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp _) hφ hK

/-- Compact C¹ localization has an actual Lebesgue L² weak derivative, equal almost
 everywhere to the product rule applied to the graph's actual derivative coordinate. -/
theorem weightedH1_compact_mul_hasWeakCoordinateDerivative {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    MemLp (fun x => χ x * weightedH1Value φ U x) 2 volume ∧
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      ((g : Space n → ℝ) =ᵐ[volume] fun x =>
        χ x * weightedH1Derivative φ i U x +
          coordinateDerivative χ i x * weightedH1Value φ U x) ∧
      HasWeakCoordinateDerivative (fun x => χ x * weightedH1Value φ U x) i g := by
  have hv : ∀ K : Set (Space n), IsCompact K →
      MemLp (weightedH1Value φ U) 2 (volume.restrict K) :=
    fun _ hK => weightedH1Value_memLp_restrict hφ.continuous U hK
  have hd : ∀ K : Set (Space n), IsCompact K →
      MemLp (weightedH1Derivative φ i U) 2 (volume.restrict K) :=
    fun _ hK => weightedH1Derivative_memLp_restrict hφ.continuous U i hK
  have hdχ := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hcv := memLp_compact_mul_of_local hχ.continuous hc hv
  have hcd := memLp_compact_mul_of_local hχ.continuous hc hd
  have hdcv := memLp_compact_mul_of_local hdχ (hasCompactSupport_coordinateDerivative hc i) hv
  have hW := hcd.add hdcv
  let w : Lp ℝ 2 volume := hW.toLp (fun x =>
    χ x * weightedH1Derivative φ i U x +
      coordinateDerivative χ i x * weightedH1Value φ U x)
  refine ⟨hcv, w, hW.coeFn_toLp, ?_⟩
  intro ψ hψ hψc
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψ2 : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  have hA : Integrable (fun x => (χ x * weightedH1Derivative φ i U x) * ψ x) volume :=
    hcd.integrable_mul hψ2
  have hB : Integrable (fun x => (coordinateDerivative χ i x * weightedH1Value φ U x) * ψ x)
      volume := hdcv.integrable_mul hψ2
  have hC : Integrable (fun x => (χ x * weightedH1Value φ U x) * coordinateDerivative ψ i x)
      volume := hcv.integrable_mul hdψ2
  have he := weightedH1_unweighted_weak_identity hφ U (hχ.mul hψ) hc.mul_right i
  have hleft : (∫ x, weightedH1Value φ U x *
      coordinateDerivative (fun y => χ y * ψ y) i x) =
      (∫ x, (coordinateDerivative χ i x * weightedH1Value φ U x) * ψ x) +
        ∫ x, (χ x * weightedH1Value φ U x) * coordinateDerivative ψ i x := by
    rw [← integral_add hB hC]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x)]
      ring
  have hright : (∫ x, weightedH1Derivative φ i U x * (χ x * ψ x)) =
      ∫ x, (χ x * weightedH1Derivative φ i U x) * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hw : (∫ x, w x * ψ x) =
      (∫ x, (χ x * weightedH1Derivative φ i U x) * ψ x) +
        ∫ x, (coordinateDerivative χ i x * weightedH1Value φ U x) * ψ x := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with x hx
    rw [show w x = χ x * weightedH1Derivative φ i U x +
      coordinateDerivative χ i x * weightedH1Value φ U x from hx]
    ring
  rw [hleft, hright] at he
  rw [hw]
  linarith

end KLS
end

#print axioms KLS.weightedH1_unweighted_weak_identity
#print axioms KLS.weightedH1Derivative_eq_zero_of_value_eq_zero
#print axioms KLS.weightedH1_eq_zero_of_value_eq_zero
#print axioms KLS.weightedH1Value_injective

#print axioms KLS.weightedH1_compact_mul_hasWeakCoordinateDerivative
