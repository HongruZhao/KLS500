import KLS.WeightedDiffusionRange
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual centered weighted gradient graph

The carrier is the closed span, in a genuine finite Hilbert sum of weighted L²
spaces, of compact C³ functions paired with their coordinate derivatives.
Its zeroth coordinate is the function with its actual mean subtracted.
Every point of the closure satisfies the weighted weak derivative identity.
No Poincaré bound, inverse operator, or regularity of a graph limit is assumed.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Function and derivative coordinates in a genuine Hilbert direct sum. -/
abbrev WeightedEnergyAmbient (φ : Space n → ℝ) :=
  PiLp 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ))

/-- The concrete smooth graph generators; the derivative coordinates are genuine derivatives. -/
def smoothCenteredGradientGraphSet (φ : Space n → ℝ) : Set (WeightedEnergyAmbient φ) :=
  {U | ∃ f : Space n → ℝ, ContDiff ℝ 3 f ∧ HasCompactSupport f ∧
    ((U 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ) =ᵐ[potentialMeasure φ]
      (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
    ∀ i : Fin n,
      ((U i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ) =ᵐ[potentialMeasure φ]
        coordinateDerivative f i}

/-- The closed linear span of the actual centered smooth gradient pairs. -/
def weightedCenteredGradientGraph (φ : Space n → ℝ) : Submodule ℝ (WeightedEnergyAmbient φ) :=
  (Submodule.span ℝ (smoothCenteredGradientGraphSet φ)).topologicalClosure

/-- The weighted energy space; its complete Hilbert structure is inherited from a closed subspace. -/
abbrev WeightedCenteredH1 (φ : Space n → ℝ) := ↥(weightedCenteredGradientGraph φ)

instance weightedCenteredH1_completeSpace (φ : Space n → ℝ) :
    CompleteSpace (WeightedCenteredH1 φ) := by
  unfold WeightedCenteredH1 weightedCenteredGradientGraph
  infer_instance

/-- The actual weighted L² function represented by a point of the graph. -/
def weightedH1Value (φ : Space n → ℝ) :
    WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0).comp
    (weightedCenteredGradientGraph φ).subtypeL

/-- The actual weighted L² weak coordinate derivative represented in the graph. -/
def weightedH1Derivative (φ : Space n → ℝ) (i : Fin n) :
    WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) i.succ).comp
    (weightedCenteredGradientGraph φ).subtypeL

@[simp] lemma weightedH1Value_apply (φ : Space n → ℝ) (U : WeightedCenteredH1 φ) :
    weightedH1Value φ U = (U : WeightedEnergyAmbient φ) 0 := rfl

@[simp] lemma weightedH1Derivative_apply (φ : Space n → ℝ)
    (U : WeightedCenteredH1 φ) (i : Fin n) :
    weightedH1Derivative φ i U = (U : WeightedEnergyAmbient φ) i.succ := rfl

/-- The inherited graph norm is the sum of the actual function and derivative L² energies. -/
theorem weightedH1_norm_sq (φ : Space n → ℝ) (U : WeightedCenteredH1 φ) :
    ‖U‖ ^ 2 = ‖weightedH1Value φ U‖ ^ 2 +
      ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 := by
  change ‖(U : WeightedEnergyAmbient φ)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

/-- The weighted formal adjoint test factor associated with one coordinate derivative. -/
def weightedDerivativeTest (φ ψ : Space n → ℝ) (i : Fin n) : Space n → ℝ :=
  fun x => coordinateDerivative ψ i x - ψ x * coordinateDerivative φ i x

lemma weightedDerivativeTest_continuous {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (i : Fin n) :
    Continuous (weightedDerivativeTest φ ψ i) :=
  (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.sub
    (hψ.continuous.mul (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous)

lemma weightedDerivativeTest_hasCompactSupport {φ ψ : Space n → ℝ}
    (hc : HasCompactSupport ψ) (i : Fin n) :
    HasCompactSupport (weightedDerivativeTest φ ψ i) :=
  (hasCompactSupport_coordinateDerivative hc i).sub hc.mul_right

lemma memLp_weightedDerivativeTest {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    MemLp (weightedDerivativeTest φ ψ i) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (weightedDerivativeTest_continuous hφ hψ i) (weightedDerivativeTest_hasCompactSupport hc i)

/-- Compact tests discharge the actual weighted integration-by-parts domain for any C¹ function. -/
theorem integral_coordinateDerivative_mul_compact_test {φ f ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, coordinateDerivative f i x * ψ x ∂potentialMeasure φ) =
      -(∫ x, f x * weightedDerivativeTest φ ψ i x ∂potentialMeasure φ) := by
  have hdψ := (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hdf := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hfg : Integrable (fun x => f x * ψ x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hψ.continuous) hc.mul_left
  have hdfg : Integrable (fun x => coordinateDerivative f i x * ψ x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hdf.mul hψ.continuous) hc.mul_left
  have hfdg : Integrable (fun x => f x * coordinateDerivative ψ i x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hdψ) (hasCompactSupport_coordinateDerivative hc i).mul_left
  have hfgdφ : Integrable (fun x => f x * ψ x * coordinateDerivative φ i x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hf.continuous.mul hψ.continuous).mul hdφ) hc.mul_left.mul_right
  have hi := integral_mul_fderiv_potentialMeasure
    (hφ.differentiable (by norm_num)) (hf.differentiable (by norm_num))
    (hψ.differentiable (by norm_num)) (EuclideanSpace.single i 1) hfg hdfg hfdg hfgdφ
  have he : (∫ x, f x * weightedDerivativeTest φ ψ i x ∂potentialMeasure φ) =
      (∫ x, f x * coordinateDerivative ψ i x ∂potentialMeasure φ) -
        (∫ x, f x * ψ x * coordinateDerivative φ i x ∂potentialMeasure φ) := by
    rw [← integral_sub hfdg hfgdφ]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [weightedDerivativeTest]; ring
  rw [he]
  change (∫ x, f x * coordinateDerivative ψ i x ∂potentialMeasure φ) =
    (∫ x, f x * ψ x * coordinateDerivative φ i x ∂potentialMeasure φ) -
      (∫ x, coordinateDerivative f i x * ψ x ∂potentialMeasure φ) at hi
  linarith

private lemma coordinateDerivative_sub_const {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (c : ℝ) (i : Fin n) :
    coordinateDerivative (fun x => f x - c) i = coordinateDerivative f i := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_sub (hf.differentiable (by norm_num) x) (differentiableAt_const c)]
  simp

/-- The two L² pairings defining the weak derivative identity form a continuous linear functional. -/
private def weightedGraphTestFunctional {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    WeightedEnergyAmbient φ →L[ℝ] ℝ :=
  (innerSL ℝ ((memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc).toLp ψ)).comp
      (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) i.succ) +
    (innerSL ℝ ((memLp_weightedDerivativeTest hφ hψ hc i).toLp
      (weightedDerivativeTest φ ψ i))).comp
      (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0)

private lemma weightedGraphTestFunctional_apply {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (i : Fin n) (U : WeightedEnergyAmbient φ) :
    weightedGraphTestFunctional hφ hψ hc i U =
      (∫ x, U i.succ x * ψ x ∂potentialMeasure φ) +
        ∫ x, U 0 x * weightedDerivativeTest φ ψ i x ∂potentialMeasure φ := by
  simp only [weightedGraphTestFunctional, add_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, innerSL_apply_apply]
  congr 1
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc).coeFn_toLp]
      with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_weightedDerivativeTest hφ hψ hc i).coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]

private lemma smoothCenteredGradientGraphSet_subset_test_ker {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    smoothCenteredGradientGraphSet φ ⊆
      LinearMap.ker (weightedGraphTestFunctional hφ hψ hc i).toLinearMap := by
  rintro U ⟨f, hf, hfc, hu, hd⟩
  change weightedGraphTestFunctional hφ hψ hc i U = 0
  rw [weightedGraphTestFunctional_apply]
  have hl : (∫ x, U i.succ x * ψ x ∂potentialMeasure φ) =
      ∫ x, coordinateDerivative f i x * ψ x ∂potentialMeasure φ :=
    integral_congr_ae ((hd i).fun_mul EventuallyEq.rfl)
  have hr : (∫ x, U 0 x * weightedDerivativeTest φ ψ i x ∂potentialMeasure φ) =
      ∫ x, (f x - ∫ y, f y ∂potentialMeasure φ) * weightedDerivativeTest φ ψ i x
        ∂potentialMeasure φ :=
    integral_congr_ae (hu.fun_mul EventuallyEq.rfl)
  rw [hl, hr]
  have hfc1 : ContDiff ℝ 1 (fun x => f x - ∫ y, f y ∂potentialMeasure φ) :=
    (hf.of_le (by norm_num)).sub contDiff_const
  have hi := integral_coordinateDerivative_mul_compact_test hφ hfc1 hψ hc i
  rw [coordinateDerivative_sub_const (hf.of_le (by norm_num))] at hi
  linarith

/-- Every element of the actual closed gradient graph satisfies weighted weak differentiation. -/
theorem weightedCenteredGradientGraph_weak_identity {φ ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, weightedH1Derivative φ i U x * ψ x ∂potentialMeasure φ) =
      -(∫ x, weightedH1Value φ U x * weightedDerivativeTest φ ψ i x ∂potentialMeasure φ) := by
  have hs : Submodule.span ℝ (smoothCenteredGradientGraphSet φ) ≤
      LinearMap.ker (weightedGraphTestFunctional hφ hψ hc i).toLinearMap :=
    Submodule.span_le.mpr (smoothCenteredGradientGraphSet_subset_test_ker hφ hψ hc i)
  have hc' := Submodule.topologicalClosure_minimal _ hs
    (weightedGraphTestFunctional hφ hψ hc i).isClosed_ker
  have hU := hc' U.property
  change weightedGraphTestFunctional hφ hψ hc i (U : WeightedEnergyAmbient φ) = 0 at hU
  rw [weightedGraphTestFunctional_apply] at hU
  simp only [weightedH1Value_apply, weightedH1Derivative_apply]
  linarith

/-- Every compact C³ function supplies its actual centered value and derivative coordinates. -/
theorem exists_weightedH1_of_smoothCompact {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ∃ U : WeightedCenteredH1 φ,
      ((weightedH1Value φ U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
      ∀ i : Fin n,
        ((weightedH1Derivative φ i U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] coordinateDerivative f i := by
  let hf2 := memLp_of_continuous_hasCompactSupport hφ hf.continuous hc
  let hd2 (i : Fin n) := memLp_of_continuous_hasCompactSupport hφ
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  let G (i : Fin n) : Lp ℝ 2 (potentialMeasure φ) := (hd2 i).toLp (coordinateDerivative f i)
  let W : WeightedEnergyAmbient φ :=
    WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure φ) F) G)
  have hW0 : ((W 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) := by
    have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
    have hi : (∫ x, F x ∂potentialMeasure φ) = ∫ x, f x ∂potentialMeasure φ := integral_congr_ae hF
    filter_upwards [CenteredL2.center_ae (potentialMeasure φ) F, hF] with x hx hy
    change (CenteredL2.center (potentialMeasure φ) F) x = _
    rw [hx, hi, hy]
  have hWi (i : Fin n) : ((W i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] coordinateDerivative f i := (hd2 i).coeFn_toLp
  have hW : W ∈ weightedCenteredGradientGraph φ :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, hc, hW0, hWi⟩)
  exact ⟨⟨W, hW⟩, hW0, hWi⟩

/-- Mean zero passes from the actual centered generators to the closed graph. -/
theorem weightedH1_integral_eq_zero {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (U : WeightedCenteredH1 φ) :
    (∫ x, weightedH1Value φ U x ∂potentialMeasure φ) = 0 := by
  let M : WeightedEnergyAmbient φ →L[ℝ] ℝ :=
    (innerSL ℝ (CenteredL2.oneLp (potentialMeasure φ))).comp
      (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0)
  have hM (W : WeightedEnergyAmbient φ) : M W = ∫ x, W 0 x ∂potentialMeasure φ :=
    CenteredL2.inner_oneLp (potentialMeasure φ) (W 0)
  have hs : smoothCenteredGradientGraphSet φ ⊆ LinearMap.ker M.toLinearMap := by
    rintro W ⟨f, hf, hc, hW, -⟩
    change M W = 0
    rw [hM, integral_congr_ae hW]
    have hfI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hf.continuous hc
    rw [integral_sub hfI (integrable_const _)]
    simp
  have hcl := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hs) M.isClosed_ker
  have hU := hcl U.property
  change M (U : WeightedEnergyAmbient φ) = 0 at hU
  rw [hM] at hU
  exact hU

end KLS
end

#print axioms KLS.weightedCenteredH1_completeSpace
#print axioms KLS.integral_coordinateDerivative_mul_compact_test
#print axioms KLS.weightedCenteredGradientGraph_weak_identity
#print axioms KLS.exists_weightedH1_of_smoothCompact
#print axioms KLS.weightedH1_integral_eq_zero
#print axioms KLS.weightedH1_norm_sq
