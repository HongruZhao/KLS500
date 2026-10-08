import KLS.WeightedEigenRegularity
import KLS.WeightedEnergyInverse

/-! Actual smooth representatives and classical equations for weighted graph Poisson solutions. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

/-- The actual graph Poisson equation becomes the ordinary local elliptic drift equation. -/
theorem weighted_poisson_unweighted_test {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 3 φ) {g : Space n → ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x) +
      (∑ i : Fin n, ∫ x, coordinateDerivative φ i x * weightedH1Derivative φ i U x * ψ x) =
      ∫ x, g x * ψ x := by
  have heq := hw (fun x => ψ x * Real.exp (φ x)) (hψ.mul hφ.exp) hc.mul_right
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
  have hright : (∫ x, g x * (ψ x * Real.exp (φ x))
      ∂potentialMeasure φ) = ∫ x, g x * ψ x := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      calc
        _ = (g x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [hcancel, mul_one]
  simpa only [hleft, hright, Finset.sum_add_distrib] using heq


/-- The actual graph weak equation and classical graph derivatives identify the pointwise Poisson equation. -/
theorem weighted_poisson_pointwise_of_representative {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    {g : Space n → ℝ} (hg : Continuous g) {U : WeightedCenteredH1 φ}
    (hw : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ)
    (hf : ContDiff ℝ 3 f) (hae : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ)) :
    ∀ x, weightedDiffusion φ f x = -g x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i U : Space n → ℝ) := (withDensity_absolutelyContinuous _ _).ae_eq
    (weightedH1_coordinateDerivative_of_representative hφ1 U hf1 hae i)
  have hcont : Continuous (fun x => weightedDiffusion φ f x + g x) :=
    (contDiff_weightedDiffusion hφ hf).continuous.add hg
  have hzero : (fun x => weightedDiffusion φ f x + g x) =ᵐ[potentialMeasure φ]
      fun _ => (0 : ℝ) := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
    intro ψ hψ hc
    have hψ3 : ContDiff ℝ 3 ψ := hψ.of_le (by simp)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have ht := hw ψ hψ3 hc
    have hD (i : Fin n) :
        (∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x ∂potentialMeasure φ) =
        ∫ x, coordinateDerivative f i x * coordinateDerivative ψ i x ∂potentialMeasure φ :=
      integral_congr_ae ((hd i).symm.mul EventuallyEq.rfl)
    simp_rw [hD] at ht
    have hgradint : (∫ x, inner ℝ (gradient ψ x) (gradient f x) ∂potentialMeasure φ) =
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
    rw [hgradint] at hi
    have hA : Integrable (fun x => ψ x * weightedDiffusion φ f x) (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hψ.continuous.mul (contDiff_weightedDiffusion hφ hf).continuous) hc.mul_right
    have hB : Integrable (fun x => ψ x * g x) (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hψ.continuous.mul hg) hc.mul_right
    have hb : (∫ x, ψ x * g x ∂potentialMeasure φ) =
        ∫ x, g x * ψ x ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    simp only [smul_eq_mul, mul_add]
    rw [integral_add hA hB, hb, hi, ht]
    ring
  have hvol := (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq hzero
  have hall : (fun x => weightedDiffusion φ f x + g x) = fun _ => (0 : ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq hvol hcont continuous_const
  intro x
  have hx := congrFun hall x
  linarith


/-- The ordinary elliptic weak formulation has the actual identity principal part and drift. -/
theorem weighted_poisson_localWeakSol {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 3 φ) {g : Space n → ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ) :
    LocalWeakSol univ (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
      (fun x i => coordinateDerivative φ i x) (fun _ => 0) g
      (weightedH1Value φ U) (fun i => weightedH1Derivative φ i U) := by
  intro ψ hψ hc _
  have h := weighted_poisson_unweighted_test hφ hw (hψ.of_le (by simp)) hc
  simp only [Measure.restrict_univ]
  have hdiag (i j : Fin n) :
      (∫ x, (1 : Matrix (Fin n) (Fin n) ℝ) i j * weightedH1Derivative φ i U x * partialD j ψ x) =
      if i = j then (∫ x, weightedH1Derivative φ i U x * partialD i ψ x) else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  simp_rw [hdiag]
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, zero_mul, integral_zero,
    add_zero, partialD, coordinateDerivative] using h

/-- Smooth forcing gives an actual globally smooth classical representative of the graph
Poisson solution. The local regularity hypotheses are supplied by its existing graph coordinates. -/
theorem weighted_poisson_exists_smooth_representative {φ g : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {U : WeightedCenteredH1 φ}
    (hw : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) = ∫ x, g x * ψ x ∂potentialMeasure φ) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) ∧
      f =ᵐ[potentialMeasure φ] (weightedH1Value φ U : Space n → ℝ) ∧
      ∀ x, weightedDiffusion φ f x = -g x := by
  have hsol : LocalWeakSol univ (weightedEigenSmoothOp hφ 0).a
      (weightedEigenSmoothOp hφ 0).b (weightedEigenSmoothOp hφ 0).c g
      (weightedH1Value φ U) (fun i => weightedH1Derivative φ i U) := by
    simpa only [weightedEigenSmoothOp, neg_zero] using
      weighted_poisson_localWeakSol (hφ.of_le (by simp)) hw
  obtain ⟨f, hs, hae⟩ := exists_contDiffOn_of_localWeakSol isOpen_univ
    (weightedEigenSmoothOp hφ 0) hg.contDiffOn
    (fun K hK _ => weightedH1Value_memLp_restrict hφ.continuous U hK)
    (fun i K hK _ => weightedH1Derivative_memLp_restrict hφ.continuous U i hK)
    (weightedH1_hasWeakGradOn_univ (hφ.of_le (by simp)) U) hsol
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hs
  have hv : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) := by
    simpa only [Measure.restrict_univ] using hae
  exact ⟨f, hf, hv, (withDensity_absolutelyContinuous _ _).ae_eq hv,
    weighted_poisson_pointwise_of_representative (hφ.of_le (by simp)) hg.continuous hw
      (hf.of_le (by simp)) hv⟩

/-- The inverse's actual compact tests identify the mean-centered forcing function. -/
theorem weightedEnergyInverse_compact_test_centered_forcing {φ g ψ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hg : MemLp g 2 (potentialMeasure φ)) (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower (hg.toLp g)) x *
        coordinateDerivative ψ i x ∂potentialMeasure φ) =
      ∫ x, (g x - ∫ y, g y ∂potentialMeasure φ) * ψ x ∂potentialMeasure φ := by
  rw [weightedEnergyInverse_compact_test hφ hκ hlower (hg.toLp g) hψ hc]
  have hrep : (∫ x, hg.toLp g x * (ψ x - ∫ y, ψ y ∂potentialMeasure φ) ∂potentialMeasure φ) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure φ) ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  rw [hrep]
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
  have hA : Integrable (fun x => g x * ψ x) (potentialMeasure φ) := hg.integrable_mul hψ2
  have hB := (hg.integrable (by norm_num)).mul_const (∫ y, ψ y ∂potentialMeasure φ)
  have hC := (hψ2.integrable (by norm_num)).const_mul (∫ y, g y ∂potentialMeasure φ)
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub hA hB, integral_sub hA hC, integral_mul_const, integral_const_mul]

/-- Every actual smooth L² forcing has a globally smooth, mean-zero classical inverse.
The density and Hessian assumptions construct the inverse; no regularity or growth of that
inverse is an input. The equation automatically removes the mean of the forcing. -/
theorem weightedEnergyInverse_exists_smooth_representative {φ g : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ)) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∫ x, f x ∂potentialMeasure φ) = 0 ∧
      (∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) ∧
      f =ᵐ[volume] (weightedH1Value φ
        (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower (hg2.toLp g)) : Space n → ℝ) ∧
      ∀ x, weightedDiffusion φ f x = -(g x - ∫ y, g y ∂potentialMeasure φ) := by
  let U := weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower (hg2.toLp g)
  have hw (ψ : Space n → ℝ) (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
      (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) =
      ∫ x, (g x - ∫ y, g y ∂potentialMeasure φ) * ψ x ∂potentialMeasure φ :=
    weightedEnergyInverse_compact_test_centered_forcing (hφ.of_le (by simp)) hκ hlower hg2 hψ hc
  obtain ⟨f, hf, hv, hvμ, heq⟩ := weighted_poisson_exists_smooth_representative hφ
    (hg.sub contDiff_const) hw
  have hf2 : MemLp f 2 (potentialMeasure φ) := (memLp_congr_ae hvμ).mpr (Lp.memLp _)
  have hm : (∫ x, f x ∂potentialMeasure φ) = 0 := by
    rw [integral_congr_ae hvμ, weightedH1_integral_eq_zero hφ.continuous U]
  have hd (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by simp)) U
        (hf.of_le (by simp)) hv i)
  exact ⟨f, hf, hf2, hm, fun i => (memLp_congr_ae (hd i)).mpr (Lp.memLp _), hv, heq⟩

end KLS
end

#print axioms KLS.weighted_poisson_unweighted_test
#print axioms KLS.weighted_poisson_exists_smooth_representative
#print axioms KLS.weightedEnergyInverse_exists_smooth_representative
