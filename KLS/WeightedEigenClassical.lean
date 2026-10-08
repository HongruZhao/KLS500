import KLS.WeightedEigenLocalEquation

/-! Actual graph derivatives and the pointwise equation of a smooth representative. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Ordinary compact-test integration by parts, with no condition on the other factor at infinity. -/
theorem integral_coordinateDerivative_mul_compact_unweighted {f ψ : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, coordinateDerivative f i x * ψ x) = -(∫ x, f x * coordinateDerivative ψ i x) := by
  have h := integral_coordinateDerivative_mul_compact_test
    (φ := fun _ => 0) contDiff_const hf hψ hc i
  simpa [potentialMeasure, weightedDerivativeTest, coordinateDerivative] using h

/-- If a graph value has a C¹ representative, its actual classical derivatives agree almost
everywhere with the already constructed graph derivatives. This is uniqueness of distributions. -/
theorem weightedH1_coordinateDerivative_of_representative {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ) (hf : ContDiff ℝ 1 f)
    (hae : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ)) (i : Fin n) :
    coordinateDerivative f i =ᵐ[volume] (weightedH1Derivative φ i U : Space n → ℝ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.locallyIntegrable
    (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
      (Lp.memLp (weightedH1Derivative φ i U)) hφ.continuous)
  intro ψ hψ hc
  have h1 := integral_coordinateDerivative_mul_compact_unweighted hf (hψ.of_le (by simp)) hc i
  have h2 := weightedH1_unweighted_weak_identity hφ U (hψ.of_le (by simp)) hc i
  have h3 : (∫ x, f x * coordinateDerivative ψ i x) =
      ∫ x, weightedH1Value φ U x * coordinateDerivative ψ i x :=
    integral_congr_ae (hae.mul EventuallyEq.rfl)
  simp only [smul_eq_mul]
  calc
    (∫ x, ψ x * coordinateDerivative f i x) = ∫ x, coordinateDerivative f i x * ψ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => mul_comm _ _
    _ = ∫ x, weightedH1Derivative φ i U x * ψ x := by linarith
    _ = ∫ x, ψ x * weightedH1Derivative φ i U x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => mul_comm _ _

/-- A C³ representative of the genuine graph eigenpair satisfies the actual diffusion equation
at every point. This helper will be applied to the representative derived by elliptic regularity. -/
theorem weighted_eigenpair_pointwise_of_representative {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    {lam : ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
      lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V))
    (hf : ContDiff ℝ 3 f) (hae : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ)) :
    ∀ x, weightedDiffusion φ f x = -lam * f x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i U : Space n → ℝ) := (withDensity_absolutelyContinuous _ _).ae_eq
    (weightedH1_coordinateDerivative_of_representative hφ1 U hf1 hae i)
  have hv : f =ᵐ[potentialMeasure φ] (weightedH1Value φ U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq hae
  have hcont : Continuous (fun x => weightedDiffusion φ f x + lam * f x) :=
    (contDiff_weightedDiffusion hφ hf).continuous.add (continuous_const.mul hf.continuous)
  have hzero : (fun x => weightedDiffusion φ f x + lam * f x) =ᵐ[potentialMeasure φ]
      fun _ => (0 : ℝ) := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
    intro ψ hψ hc
    have hψ3 : ContDiff ℝ 3 ψ := hψ.of_le (by simp)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have ht := weighted_eigenpair_compact_test hφ.continuous hw hψ3 hc
    have hD (i : Fin n) :
        (∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x ∂potentialMeasure φ) =
        ∫ x, coordinateDerivative f i x * coordinateDerivative ψ i x ∂potentialMeasure φ :=
      integral_congr_ae ((hd i).symm.mul EventuallyEq.rfl)
    have hV : (∫ x, weightedH1Value φ U x * ψ x ∂potentialMeasure φ) =
        ∫ x, f x * ψ x ∂potentialMeasure φ :=
      integral_congr_ae (hv.symm.mul EventuallyEq.rfl)
    simp_rw [hD, hV] at ht
    have hg : (∫ x, inner ℝ (gradient ψ x) (gradient f x) ∂potentialMeasure φ) =
        ∑ i : Fin n, ∫ x, coordinateDerivative f i x * coordinateDerivative ψ i x
          ∂potentialMeasure φ := by
      simp_rw [← sum_coordinateDerivative_mul]
      rw [integral_finsetSum (f := fun i x => coordinateDerivative ψ i x * coordinateDerivative f i x) Finset.univ (fun i _ =>
        integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
          ((contDiff_coordinateDerivative hψ1 (m := 0) (by norm_num) i).continuous.mul
            (contDiff_coordinateDerivative hf1 (m := 0) (by norm_num) i).continuous)
          (hasCompactSupport_coordinateDerivative hc i).mul_right)]
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => mul_comm _ _
    have hi := integral_mul_weightedDiffusion_of_hasCompactSupport_left hφ1 hψ1
      (hf.of_le (by norm_num)) hc
    rw [hg] at hi
    have hA : Integrable (fun x => ψ x * weightedDiffusion φ f x) (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hψ.continuous.mul (contDiff_weightedDiffusion hφ hf).continuous) hc.mul_right
    have hB : Integrable (fun x => ψ x * (lam * f x)) (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hψ.continuous.mul (continuous_const.mul hf.continuous)) hc.mul_right
    have hb : (∫ x, ψ x * (lam * f x) ∂potentialMeasure φ) =
        lam * ∫ x, f x * ψ x ∂potentialMeasure φ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    simp only [smul_eq_mul, mul_add]
    rw [integral_add hA hB, hb, hi, ht]
    ring
  have hvol := (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq hzero
  have hall : (fun x => weightedDiffusion φ f x + lam * f x) = fun _ => (0 : ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq hvol hcont continuous_const
  intro x
  have hx := congrFun hall x
  linarith

end KLS
end

#print axioms KLS.weightedH1_coordinateDerivative_of_representative

#print axioms KLS.weighted_eigenpair_pointwise_of_representative
