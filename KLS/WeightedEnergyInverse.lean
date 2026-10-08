import KLS.WeightedEnergyCoercivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual weighted energy inverse

Lax–Milgram inverts the proved coercive form on the actual complete gradient
graph. The value projection's Hilbert adjoint supplies the actual L² forcing.
The result is a bounded linear solution map, with genuine variational and
compact-test identities; no unbounded spectral operator is postulated.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The bounded solution map for the actual weighted Dirichlet form. -/
def weightedEnergyInverse {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] WeightedCenteredH1 φ :=
  (weightedEnergyForm_isCoercive hφ hκ hlower).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (weightedH1Value φ).adjoint

/-- The inverse satisfies the genuine variational equation against every energy-space element. -/
theorem weightedEnergyInverse_variational {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ (weightedEnergyInverse hφ hκ hlower g) V =
      inner ℝ g (weightedH1Value φ V) := by
  let hc := weightedEnergyForm_isCoercive hφ hκ hlower
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((weightedH1Value φ).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

/-- The variational solution is unique in the actual weighted energy space. -/
theorem weightedEnergyInverse_unique {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) {U : WeightedCenteredH1 φ}
    (hU : ∀ V, weightedEnergyForm φ U V = inner ℝ g (weightedH1Value φ V)) :
    U = weightedEnergyInverse hφ hκ hlower g := by
  let hc := weightedEnergyForm_isCoercive hφ hκ hlower
  have he : (weightedH1Value φ).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((weightedH1Value φ).adjoint g) := by rw [he]
    _ = weightedEnergyInverse hφ hκ hlower g := rfl

/-- Every actual L² forcing has exactly one solution of the energy variational equation. -/
theorem existsUnique_weightedEnergySolution {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ∃! U : WeightedCenteredH1 φ,
      ∀ V, weightedEnergyForm φ U V = inner ℝ g (weightedH1Value φ V) := by
  exact ⟨weightedEnergyInverse hφ hκ hlower g,
    weightedEnergyInverse_variational hφ hκ hlower g,
    fun _ hU => weightedEnergyInverse_unique hφ hκ hlower g hU⟩

/-- Testing with the solution gives the actual energy identity. -/
theorem weightedEnergyInverse_energy_identity {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∑ i : Fin n, ‖weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) =
      inner ℝ g (weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)) := by
  rw [← weightedEnergyForm_self]
  exact weightedEnergyInverse_variational hφ hκ hlower g _



/-- The value of the actual solution has the expected reciprocal-Hessian L² bound. -/
theorem weightedEnergyInverse_value_norm_le {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)‖ ≤ κ⁻¹ * ‖g‖ := by
  let U := weightedEnergyInverse hφ hκ hlower g
  have hP := weightedH1_value_norm_sq_le_energy hφ hκ hlower U
  have hE := weightedEnergyInverse_energy_identity hφ hκ hlower g
  change (∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2) = inner ℝ g (weightedH1Value φ U) at hE
  rw [hE] at hP
  have hinner := real_inner_le_norm g (weightedH1Value φ U)
  have hm := mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hκ.le)
  change ‖weightedH1Value φ U‖ ≤ κ⁻¹ * ‖g‖
  by_cases hz : ‖weightedH1Value φ U‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖weightedH1Value φ U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := ‖weightedH1Value φ U‖) ?_ hp
    nlinarith

/-- The actual derivative energy of the solution is bounded by the forcing norm. -/
theorem weightedEnergyInverse_energy_le {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∑ i : Fin n, ‖weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
      κ⁻¹ * ‖g‖ ^ 2 := by
  rw [weightedEnergyInverse_energy_identity]
  calc
    _ ≤ ‖g‖ * ‖weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * (κ⁻¹ * ‖g‖) :=
      mul_le_mul_of_nonneg_left (weightedEnergyInverse_value_norm_le hφ hκ hlower g) (norm_nonneg g)
    _ = _ := by ring

/-- The actual value of every inverse image has mean zero. -/
theorem weightedEnergyInverse_integral_eq_zero {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∫ x, weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g) x
      ∂potentialMeasure φ) = 0 :=
  weightedH1_integral_eq_zero hφ.continuous _

/-- The inverse obeys the actual compact-test weak Poisson equation, with the mean
 of the forcing removed by the test function's genuine centering. -/
theorem weightedEnergyInverse_compact_test {φ ψ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) x *
        coordinateDerivative ψ i x ∂potentialMeasure φ) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure φ) ∂potentialMeasure φ := by
  obtain ⟨V, hV, hdV⟩ := exists_weightedH1_of_smoothCompact hφ.continuous hψ hc
  have he := weightedEnergyInverse_variational hφ hκ hlower g V
  rw [weightedEnergyForm_eq_sum_integral] at he
  have hleft : (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) x *
        weightedH1Derivative φ i V x ∂potentialMeasure φ) =
      ∑ i : Fin n, ∫ x,
        weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) x *
          coordinateDerivative ψ i x ∂potentialMeasure φ := by
    apply Finset.sum_congr rfl
    intro i _
    exact integral_congr_ae (EventuallyEq.rfl.fun_mul (hdV i))
  have hright : inner ℝ g (weightedH1Value φ V) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure φ) ∂potentialMeasure φ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hV] with x hx
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx]
    ring
  rw [hleft, hright] at he
  exact he

/-- Mean-zero forcing yields the actual weak equation `-Lφ u = g` on compact C³ tests. -/
theorem weightedEnergyInverse_compact_test_of_integral_eq_zero {φ ψ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (hg : (∫ x, g x ∂potentialMeasure φ) = 0)
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) x *
        coordinateDerivative ψ i x ∂potentialMeasure φ) =
      ∫ x, g x * ψ x ∂potentialMeasure φ := by
  rw [weightedEnergyInverse_compact_test hφ hκ hlower g hψ hc]
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
  have hI : Integrable (fun x => g x * ψ x) (potentialMeasure φ) :=
    (Lp.memLp g).integrable_mul hψ2
  have hC := ((Lp.memLp g).integrable (by norm_num)).mul_const (∫ y, ψ y ∂potentialMeasure φ)
  calc
    _ = ∫ x, (g x * ψ x - g x * ∫ y, ψ y ∂potentialMeasure φ) ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by rw [integral_sub hI hC, integral_mul_const, hg, zero_mul, sub_zero]


/-- The actual weak graph identity identifies the Dirichlet test pairing with weighted diffusion. -/
theorem weightedH1_gradient_test_eq_neg_diffusion {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x
      ∂potentialMeasure φ) =
      -(∫ x, weightedH1Value φ U x * weightedDiffusion φ ψ x ∂potentialMeasure φ) := by
  have hdψ (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative ψ i) :=
    contDiff_coordinateDerivative hψ (by norm_num) i
  have hcψ (i : Fin n) : HasCompactSupport (coordinateDerivative ψ i) :=
    hasCompactSupport_coordinateDerivative hc i
  have hi (i : Fin n) : Integrable (fun x => weightedH1Value φ U x *
      weightedDerivativeTest φ (coordinateDerivative ψ i) i x) (potentialMeasure φ) :=
    (Lp.memLp _).integrable_mul (memLp_weightedDerivativeTest hφ (hdψ i) (hcψ i) i)
  calc
    _ = ∑ i : Fin n, -(∫ x, weightedH1Value φ U x *
        weightedDerivativeTest φ (coordinateDerivative ψ i) i x ∂potentialMeasure φ) := by
      exact Finset.sum_congr rfl (fun i _ =>
        weightedCenteredGradientGraph_weak_identity hφ U (hdψ i) (hcψ i) i)
    _ = -(∫ x, ∑ i : Fin n, weightedH1Value φ U x *
        weightedDerivativeTest φ (coordinateDerivative ψ i) i x ∂potentialMeasure φ) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum Finset.univ (fun i _ => hi i)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.mul_sum]
        congr 1
        simp only [weightedDerivativeTest, weightedDiffusion_eq_sum, coordinateHessian]

/-- Mean-zero forcing solves the actual distribution equation using the actual function value. -/
theorem weightedEnergyInverse_weak_diffusion {φ ψ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (hg : (∫ x, g x ∂potentialMeasure φ) = 0)
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g) x *
      (-weightedDiffusion φ ψ x) ∂potentialMeasure φ) =
      ∫ x, g x * ψ x ∂potentialMeasure φ := by
  have he := weightedH1_gradient_test_eq_neg_diffusion (hφ.of_le (by norm_num))
    (weightedEnergyInverse hφ hκ hlower g) (hψ.of_le (by norm_num)) hc
  have hs := weightedEnergyInverse_compact_test_of_integral_eq_zero hφ hκ hlower g hg hψ hc
  calc
    _ = -(∫ x, weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g) x *
        weightedDiffusion φ ψ x ∂potentialMeasure φ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := he.symm.trans hs

end KLS
end

#print axioms KLS.weightedEnergyInverse
#print axioms KLS.weightedEnergyInverse_variational
#print axioms KLS.weightedEnergyInverse_unique
#print axioms KLS.existsUnique_weightedEnergySolution
#print axioms KLS.weightedEnergyInverse_energy_identity

#print axioms KLS.weightedEnergyInverse_compact_test
#print axioms KLS.weightedEnergyInverse_compact_test_of_integral_eq_zero

#print axioms KLS.weightedEnergyInverse_value_norm_le
#print axioms KLS.weightedEnergyInverse_energy_le

#print axioms KLS.weightedH1_gradient_test_eq_neg_diffusion
#print axioms KLS.weightedEnergyInverse_weak_diffusion
