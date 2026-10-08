/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.Garding
public import EllipticPdes.Regularity.DiffQuotientBound
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Caccioppoli (interior energy) estimate

The first-derivative interior estimate: for a weak solution of `L u = f`, the energy
`∫_V |∇u|²` is bounded by the data on a slightly larger set `W`. Obtained by testing
the weak formulation with `ζ² u`, using uniform ellipticity from below and Young's
inequality to absorb the gradient term. See Gilbarg-Trudinger, *Elliptic PDE of
Second Order*, Theorem 8.8, and Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1.

## Cutoff-multiplication keystone

The test function `ζ² u` for `u ∈ H₀¹(Ω)` is not directly available from the graph
encoding of `Sobolev/Basic.lean`. We build it here. For a smooth compactly supported
cutoff `η` (an [`IsTestFn`]) we assemble the **cutoff-multiplication operator** on the
ambient graph space,

  `(cutoffMul η U)₀ = η · U₀`,   `(cutoffMul η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`,

which is exactly the Leibniz rule `∇(η u) = η ∇u + (∇η) u`. It is a bounded operator, it
sends the graph of a test function `φ` to the graph of the product `η φ`, hence by
closure it maps `H₀¹(Ω)` into itself: [`cutoffMul_mem_H01`].

## Estimates shared by the energy bounds

`IsTestFn.supNorm` is the supremum norm of a test function. `absorb_energy` is the Peter-Paul
absorption `λ e² ≤ K₁ N e + K₂ N² ⟹ (λ/2) e² ≤ (K₁²/(2λ) + K₂) N²` that closes the Caccioppoli
estimate and the difference-quotient energy estimate, and `neg_cross_sum_le` bounds the cross
term both of them produce.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-- A continuous function with compact support is bounded in absolute value by the supremum of
its absolute value. -/
lemma HasCompactSupport.abs_le_iSup_abs {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hc : Continuous f) (hs : HasCompactSupport f) (x : X) : |f x| ≤ ⨆ y, |f y| := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact le_ciSup (f := fun y => |f y|)
    ⟨C, by rintro _ ⟨y, rfl⟩; simpa only [Real.norm_eq_abs] using hC y⟩ x

/-- The supremum of the absolute value of a continuous function with compact support is
nonnegative. -/
lemma HasCompactSupport.iSup_abs_nonneg {X : Type*} [TopologicalSpace X] [Nonempty X]
    {f : X → ℝ} (hc : Continuous f) (hs : HasCompactSupport f) : 0 ≤ ⨆ y, |f y| :=
  (abs_nonneg _).trans (hs.abs_le_iSup_abs hc (Classical.arbitrary X))

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The supremum norm `sup |φ|` of a test function. -/
def IsTestFn.supNorm {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (_ : IsTestFn Ω φ) : ℝ :=
  ⨆ x, |φ x|

/-- The supremum norm of the `i`-th partial derivative `sup |∂ᵢφ|` of a test function. -/
def IsTestFn.partialSupNorm {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (_ : IsTestFn Ω φ) (i : Fin d) : ℝ :=
  ⨆ x, |partialD i φ x|

/-- A test function is bounded in absolute value by its supremum norm. -/
lemma IsTestFn.abs_le_supNorm {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (x : EuclideanSpace ℝ (Fin d)) :
    |φ x| ≤ h.supNorm :=
  h.2.1.abs_le_iSup_abs h.continuous x

/-- The supremum norm of a test function is nonnegative. -/
lemma IsTestFn.supNorm_nonneg {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) : 0 ≤ h.supNorm :=
  h.2.1.iSup_abs_nonneg h.continuous

/-- A partial derivative of a test function is bounded in absolute value by its supremum
norm. -/
lemma IsTestFn.abs_partialD_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : |partialD i φ x| ≤ h.partialSupNorm i :=
  (h.hasCompactSupport_partialD i).abs_le_iSup_abs (h.continuous_partialD i) x

/-- The supremum norm of a partial derivative of a test function is nonnegative. -/
lemma IsTestFn.partialSupNorm_nonneg {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    0 ≤ h.partialSupNorm i :=
  (h.hasCompactSupport_partialD i).iSup_abs_nonneg (h.continuous_partialD i)

end EllipticPdes.Sobolev

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Multiplier actions of a cutoff on `L²(Ω)` -/

/-- **Multiplication by a cutoff** on `L²(Ω)`, as a continuous linear map. The cutoff `η` is a
test function on some set `Ω'` unrelated to `Ω`, so its support may meet `∂Ω`; only smoothness
and compact support of `η` are used. -/
def mulCutoff (Ω : Set (EuclideanSpace ℝ (Fin d))) {Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω' η) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL hη.continuous.measurable (ae_of_all (volume.restrict Ω) hη.abs_le_supNorm)

/-- Multiplication by the partial `∂ᵢη` of a cutoff on `L²(Ω)`, the companion of `mulCutoff`
that carries the Leibniz correction term. -/
def mulCutoffPartial (Ω : Set (EuclideanSpace ℝ (Fin d)))
    {Ω' : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω' η) (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (hη.continuous_partialD i).measurable
    (ae_of_all (volume.restrict Ω) (hη.abs_partialD_le i))

/-- Multiplication by a cutoff that is a test function of the domain itself. -/
abbrev mulTest {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : L2D Ω →L[ℝ] L2D Ω :=
  mulCutoff Ω h

/-- Multiplication by `∂ᵢη` for a cutoff that is a test function of the domain itself. -/
abbrev mulTestPartial {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCutoffPartial Ω h i

/-- The a.e. representative of `mulCutoff`: `mulCutoff Ω hη g =ᵐ x ↦ η x · g x`. -/
lemma mulCutoff_coeFn {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω' η) (g : L2D Ω) :
    mulCutoff Ω hη g =ᵐ[volume.restrict Ω] fun x => η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- The a.e. representative of `mulCutoffPartial`:
`mulCutoffPartial Ω hη i g =ᵐ x ↦ ∂ᵢη x · g x`. -/
lemma mulCutoffPartial_coeFn {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω' η) (i : Fin d) (g : L2D Ω) :
    mulCutoffPartial Ω hη i g =ᵐ[volume.restrict Ω] fun x => partialD i η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-! ### Cutoff-multiplication operator on the graph space -/

/-- The **cutoff-multiplication operator** `cutoffMulOn Ω η : H1amb Ω →L H1amb Ω`, encoding
the Leibniz rule `∇(η u) = η ∇u + (∇η) u`: coordinate `0` multiplies by `η`, coordinate `i+1`
sends `U` to `η · U_{i+1} + (∂ᵢη) · U₀`. -/
def cutoffMulOn (Ω : Set (EuclideanSpace ℝ (Fin d))) {Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω' η) : H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi
        (Fin.cons ((mulCutoff Ω h).comp (ContinuousLinearMap.proj 0))
          (fun i => (mulCutoff Ω h).comp (ContinuousLinearMap.proj i.succ)
            + (mulCutoffPartial Ω h i).comp (ContinuousLinearMap.proj 0)))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).toContinuousLinearMap)

/-- The cutoff-multiplication operator for a cutoff that is a test function of the domain
itself. -/
abbrev cutoffMul {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : H1amb Ω →L[ℝ] H1amb Ω :=
  cutoffMulOn Ω h

/-- Coordinate `0` of `cutoffMulOn`: `(cutoffMulOn Ω η U)₀ = η · U₀`. -/
lemma cutoffMulOn_apply_zero {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω' η) (U : H1amb Ω) :
    (cutoffMulOn Ω h U) 0 = mulCutoff Ω h (U 0) := by
  simp only [cutoffMulOn, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_zero, ContinuousLinearMap.proj_apply]

/-- Coordinate `i+1` of `cutoffMulOn`:
`(cutoffMulOn Ω η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`. -/
lemma cutoffMulOn_apply_succ {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω' η) (U : H1amb Ω) (i : Fin d) :
    (cutoffMulOn Ω h U) i.succ = mulCutoff Ω h (U i.succ) + mulCutoffPartial Ω h i (U 0) := by
  simp only [cutoffMulOn, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_succ, _root_.add_apply, ContinuousLinearMap.proj_apply]

/-! ### Leibniz product rule and stability of test functions under products -/

/-- The classical Leibniz rule for the `i`-th partial of a product:
`∂ᵢ(η φ) = η ∂ᵢφ + (∂ᵢη) φ`. -/
lemma partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : Differentiable ℝ η) (hφ : Differentiable ℝ φ) (i : Fin d) :
    partialD i (fun x => η x * φ x)
      = fun x => η x * partialD i φ x + partialD i η x * φ x := by
  funext x
  simp only [partialD]
  rw [fderiv_fun_mul (hη x) (hφ x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- The pointwise product of two test functions is a test function: smoothness is
`ContDiff.mul`, the support of the product sits inside `tsupport φ ⊆ Ω`, and compact
support is inherited from `φ`. -/
lemma isTestFn_mul {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    IsTestFn Ω (fun x => η x * φ x) := by
  refine ⟨hη.1.mul hφ.1, ?_, ?_⟩
  · exact HasCompactSupport.mul_left (f' := φ) (f := η) hφ.2.1
  · exact (closure_mono (Function.support_mul_subset_right η φ)).trans hφ.2.2

/-! ### Test-function calculus -/

/-- The partial derivative of a `C^∞` function is `C^∞`. -/
theorem contDiff_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
  exact hf.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))

/-- The partial derivative of a compactly-supported function has compact support. -/
theorem hasCompactSupport_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) : HasCompactSupport (partialD j φ) :=
  hφ.mono' ((subset_tsupport (partialD j φ)).trans (tsupport_partialD_subset j φ))

/-- `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function on `V` when `φ` is. -/
theorem isTest_partialD {V : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hV : tsupport φ ⊆ V) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) ∧ HasCompactSupport (partialD j φ)
      ∧ tsupport (partialD j φ) ⊆ V :=
  ⟨contDiff_partialD hc j, hasCompactSupport_partialD hcs j,
    (tsupport_partialD_subset j φ).trans hV⟩

/-! ### Cutoff multiplication sending a graph to the product graph -/

/-- **Keystone (graphs).** The cutoff-multiplication operator sends the graph of a test
function `φ` to the graph of the product `η φ`: `cutoffMul η (graph φ) = graph (η φ)`. This
is the Leibniz rule realised at the level of `L²` classes, and it is what lets `cutoffMul`
extend from test functions to `H₀¹(Ω)` by closure. -/
lemma cutoffMul_testGraph {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    cutoffMul hη hφ.testGraph = (isTestFn_mul hη hφ).testGraph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- coordinate 0: `η · [φ] = [η φ]`
    rw [cutoffMulOn_apply_zero, IsTestFn.testGraph_zero, IsTestFn.testGraph_zero]
    apply Lp.ext
    filter_upwards [mulCutoff_coeFn hη hφ.testCls, hφ.mem_lp.coeFn_toLp,
      (isTestFn_mul hη hφ).mem_lp.coeFn_toLp] with x hx hφx hprod
    rw [hx, show (hφ.testCls x : ℝ) = φ x from hφx]
    exact hprod.symm
  · -- coordinate `i+1`: `η · [∂ᵢφ] + (∂ᵢη) · [φ] = [∂ᵢ(η φ)]`
    rw [cutoffMulOn_apply_succ, IsTestFn.testGraph_succ, IsTestFn.testGraph_zero,
      IsTestFn.testGraph_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulTest hη (hφ.partialCls i))
        (mulTestPartial hη i hφ.testCls),
      mulCutoff_coeFn hη (hφ.partialCls i), mulCutoffPartial_coeFn hη i hφ.testCls,
      (hφ.memLp_partialD i).coeFn_toLp, hφ.mem_lp.coeFn_toLp,
      ((isTestFn_mul hη hφ).memLp_partialD i).coeFn_toLp] with
      x hadd hmt hmtp hpφ hφx hprodp
    rw [hadd, Pi.add_apply, hmt, hmtp]
    change η x * (hφ.partialCls i x : ℝ) + partialD i η x * (hφ.testCls x : ℝ)
      = ((isTestFn_mul hη hφ).partialCls i) x
    rw [show (hφ.partialCls i x : ℝ) = partialD i φ x from hpφ,
      show (hφ.testCls x : ℝ) = φ x from hφx,
      show ((isTestFn_mul hη hφ).partialCls i) x = partialD i (fun y => η y * φ y) x from hprodp,
      congrFun (partialD_mul (hη.1.differentiable (by simp))
        (hφ.1.differentiable (by simp)) i) x]

/-! ### Preservation of `H₀¹(Ω)` under cutoff multiplication -/

/-- **Keystone (membership).** The cutoff-multiplication operator maps `H₀¹(Ω)` into
itself. Since `cutoffMul η` is continuous and sends every test-function graph into
`H₀¹(Ω)` (by [`cutoffMul_testGraph`]), it maps the closure `H₀¹(Ω)` into the closed set
`H₀¹(Ω)`. -/
lemma cutoffMul_mem_H01 {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) {U : H1amb Ω}
    (hU : U ∈ H01 Ω) : cutoffMul hη U ∈ H01 Ω := by
  have hle : (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure
      ≤ Submodule.comap (cutoffMul hη).toLinearMap (H01 Ω) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change cutoffMul hη hφ.testGraph ∈ H01 Ω
      rw [cutoffMul_testGraph hη hφ]
      exact (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨_, isTestFn_mul hη hφ, rfl⟩)
    · exact IsClosed.preimage (cutoffMul hη).continuous
        (Submodule.isClosed_topologicalClosure _)
  exact Submodule.mem_comap.mp (hle hU)

/-! ### Weighted energy lower bound from ellipticity -/

/-- **Ellipticity energy bound for an arbitrary `L²` gradient family.** The lower bound of
[`EllipticCoeff.bilin_self_ge`] uses only the `L²` classes, not the weak-gradient
relation, so it holds for any family `g : Fin d → L²(Ω)`:
`λ ∑ᵢ ‖gᵢ‖² ≤ ∑ᵢⱼ ⟪aᵢⱼ gᵢ, gⱼ⟫`. Applied to `gᵢ = ζ · ∂ᵢu` this is the cutoff-weighted
energy lower bound `λ ∫_Ω ζ² |∇u|² ≤ ∫_Ω ζ² ∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼu` driving the Caccioppoli
estimate (Evans, *PDE* 2nd ed., §6.3.1). -/
lemma energy_ge (A : EllipticCoeff d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (g : Fin d → L2D Ω) :
    A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      ≤ ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := by
  have hPint : Integrable (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      (volume.restrict Ω) :=
    (integrable_finsetSum _ (fun i _ => integrable_sq (g i))).const_mul A.lam
  have hpoint : (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      ≤ᵐ[volume.restrict Ω] fun x => ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
    (ae_restrict_of_ae A.elliptic).mono (fun x hx => hx (fun i => g i x))
  have hlamS : ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2
      = A.lam * ∑ i : Fin d, ‖g i‖ ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_sq (g i))]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => sq_integral_eq_norm_sq (g i))
  have hRHS : ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫
      = ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
    exact Finset.sum_congr rfl (fun j _ => A.inner_actL_eq i j _ _)
  calc A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      = ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2 := hlamS.symm
    _ ≤ ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
          A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
        integral_mono_ae hPint (integrable_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => A.integrable_triple i j _ _))) hpoint
    _ = ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := hRHS.symm

/-! ### Operator-norm bounds and regrouping identities for the cutoff -/

/-- Operator-norm bound for the cutoff multiplier: `‖η · g‖ ≤ ‖η‖∞ · ‖g‖`. -/
lemma norm_mulTest_le_supNorm {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (g : L2D Ω) :
    ‖mulTest h g‖ ≤ h.supNorm * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Operator-norm bound for the partial-cutoff multiplier: `‖∂ᵢη · g‖ ≤ ‖∂ᵢη‖∞ · ‖g‖`. -/
lemma norm_mulTestPartial_le_supNorm {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (i : Fin d) (g : L2D Ω) :
    ‖mulTestPartial h i g‖ ≤ h.partialSupNorm i * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Regrouping one `ζ` factor across the coefficient action, principal part:
`⟪aᵢⱼ (ζ p), ζ q⟫ = ⟪aᵢⱼ p, ζ² q⟫`. -/
lemma actL_mulTest_regroup (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j (mulTest hζ p), mulTest hζ q⟫
      = ⟪A.actL i j p, mulTest (isTestFn_mul hζ hζ) q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq]
  refine integral_congr_ae ?_
  filter_upwards [mulCutoff_coeFn hζ p, mulCutoff_coeFn hζ q,
    mulCutoff_coeFn (isTestFn_mul hζ hζ) q] with x hp hq hpq
  rw [hp, hq, hpq]
  ring

/-- Regrouping the cross term: moving one `ζ` off `∂ⱼ(ζ²) = 2 ζ ∂ⱼζ` onto `p`,
`⟪aᵢⱼ p, ∂ⱼ(ζ²) q⟫ = 2 ⟪aᵢⱼ (ζ p), ∂ⱼζ q⟫`. -/
lemma actL_cross_regroup (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j p, mulTestPartial (isTestFn_mul hζ hζ) j q⟫
      = 2 * ⟪A.actL i j (mulTest hζ p), mulTestPartial hζ j q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [mulCutoffPartial_coeFn (isTestFn_mul hζ hζ) j q,
    mulCutoff_coeFn hζ p, mulCutoffPartial_coeFn hζ j q] with x hpart hp hq
  rw [hpart, hp, hq,
    congrFun (partialD_mul (hζ.1.differentiable (by simp))
      (hζ.1.differentiable (by simp)) j) x]
  ring

/-! ### Estimates shared by the energy bounds -/

/-- The inner product on `L²(Ω)` is the integral of the product over `Ω`. -/
lemma inner_eq_setIntegral {Ω : Set (EuclideanSpace ℝ (Fin d))} (f g : L2D Ω) :
    ⟪f, g⟫ = ∫ x in Ω, (f x : ℝ) * (g x : ℝ) := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => Real.inner_apply _ _)

/-- Cauchy-Schwarz for a finite sum of reals: `∑ xᵢ ≤ √d · √(∑ xᵢ²)`. -/
lemma sum_le_sqrt_card_mul_sqrt_sum_sq (x : Fin d → ℝ) :
    ∑ i, x i ≤ Real.sqrt d * Real.sqrt (∑ i, x i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)

/-- **Absorption.** If `λ e² ≤ K₁ N e + K₂ N²`, then `(λ/2) e² ≤ (K₁²/(2λ) + K₂) N²`: the
Peter-Paul inequality moves half of the left-hand side across. -/
lemma absorb_energy {lam e N K₁ K₂ : ℝ} (hlam : 0 < lam)
    (h : lam * e ^ 2 ≤ K₁ * N * e + K₂ * N ^ 2) :
    lam / 2 * e ^ 2 ≤ (K₁ ^ 2 / (2 * lam) + K₂) * N ^ 2 := by
  have hy := young_peterPaul (lam := lam) (B := K₁) (x := e) (y := N) hlam
  nlinarith only [h, hy]

/-- Square-root form of a quadratic bound: `x² ≤ c P²` gives `x ≤ √c P`. -/
lemma le_sqrt_mul_of_sq_le {x c P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P) (h : x ^ 2 ≤ c * P ^ 2) :
    x ≤ Real.sqrt c * P := by
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (c * P ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt c * P := by rw [Real.sqrt_mul' c (sq_nonneg P), Real.sqrt_sq hP]

/-- The sum of two coefficient actions on `L²(Ω)` is the pointwise sum of the products, almost
everywhere. -/
theorem mulCoeffL_add_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ} (hm₁ : Measurable f₁)
    {M₁ : ℝ} (hb₁ : ∀ᵐ x ∂(volume.restrict Ω), |f₁ x| ≤ M₁) (hm₂ : Measurable f₂) {M₂ : ℝ}
    (hb₂ : ∀ᵐ x ∂(volume.restrict Ω), |f₂ x| ≤ M₂) (g h : L2D Ω) :
    mulCoeffL hm₁ hb₁ g + mulCoeffL hm₂ hb₂ h
      =ᵐ[volume.restrict Ω] fun x => f₁ x * (g x : ℝ) + f₂ x * (h x : ℝ) := by
  filter_upwards [Lp.coeFn_add (mulCoeffL hm₁ hb₁ g) (mulCoeffL hm₂ hb₂ h),
    mulCoeffL_coeFn hm₁ hb₁ g, mulCoeffL_coeFn hm₂ hb₂ h] with x hadd h1 h2
  simp only [hadd, h1, h2, Pi.add_apply]

/-- The pairing of two vectors is bounded from below by minus the product of the norms. -/
lemma neg_real_inner_le_mul_norm {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (w v : G) : -⟪w, v⟫ ≤ ‖w‖ * ‖v‖ :=
  (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

/-- Regrouping the transport term: `⟪bᵢ p, ζ² q⟫ = ⟪bᵢ (ζ p), ζ q⟫`. -/
lemma bAct_transport_regroup (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i : Fin d) (p q : L2D Ω) :
    ⟪Op.bAct i p, mulTest (isTestFn_mul hζ hζ) q⟫
      = ⟪Op.bAct i (mulTest hζ p), mulTest hζ q⟫ := by
  simp only [FullEllipticOp.bAct]
  rw [inner_mulCoeffL_eq, inner_mulCoeffL_eq]
  refine integral_congr_ae ?_
  filter_upwards [mulCutoff_coeFn (isTestFn_mul hζ hζ) q, mulCutoff_coeFn hζ p,
    mulCutoff_coeFn hζ q] with x hq2 hp hq
  rw [hq2, hp, hq]
  ring

/-- **Cross term bound.** `-∑ᵢⱼ 2 ⟪aᵢⱼ (ζ pᵢ), ∂ⱼζ q⟫ ≤ 2Λ ‖q‖ (∑ᵢ ‖ζ pᵢ‖) (∑ⱼ ‖∂ⱼζ‖∞)`. -/
lemma neg_cross_sum_le (A : EllipticCoeff d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (p : Fin d → L2D Ω) (q : L2D Ω) :
    -∑ i : Fin d, ∑ j : Fin d, 2 * ⟪A.actL i j (mulTest hζ (p i)), mulTestPartial hζ j q⟫
      ≤ 2 * A.Λ * ‖q‖ * ((∑ i : Fin d, ‖mulTest hζ (p i)‖)
        * ∑ j : Fin d, hζ.partialSupNorm j) := by
  rw [← Finset.sum_neg_distrib, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := neg_real_inner_le_mul_norm (A.actL i j (mulTest hζ (p i)))
    (mulTestPartial hζ j q)
  have h2 : ‖A.actL i j (mulTest hζ (p i))‖ * ‖mulTestPartial hζ j q‖
      ≤ (A.Λ * ‖mulTest hζ (p i)‖) * (hζ.partialSupNorm j * ‖q‖) :=
    mul_le_mul (A.norm_actL_le i j _) (norm_mulTestPartial_le_supNorm hζ j q)
      (norm_nonneg _) (mul_nonneg A.Λ_nonneg (norm_nonneg _))
  nlinarith only [h1, h2]

/-! ### Interior energy (Caccioppoli) estimate -/

/-- The weak identity of `U` against the test element `ζ² U`, with the pairing expanded into
principal, transport and zeroth-order inner products, and the datum `f` on the right. -/
def TestedIdentity (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (U : H1amb Ω) (f : L2D Ω) : Prop :=
  (∑ i : Fin d, ∑ j : Fin d, ⟪Op.toEllipticCoeff.actL i j (U i.succ),
        cutoffMul (isTestFn_mul hζ hζ) U j.succ⟫)
    + (∑ i : Fin d, ⟪Op.bAct i (U i.succ), cutoffMul (isTestFn_mul hζ hζ) U 0⟫)
    + ⟪Op.cAct (U 0), cutoffMul (isTestFn_mul hζ hζ) U 0⟫
  = ∫ x in Ω, (f x : ℝ) * (cutoffMul (isTestFn_mul hζ hζ) U 0 x : ℝ)

/-- A weak solution `u ∈ H₀¹(Ω)` satisfies the identity against `ζ² u`, which lies in `H₀¹(Ω)`
by [`cutoffMul_mem_H01`]. -/
lemma testedIdentity_of_H01 (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) :
    TestedIdentity Op hζ (u : H1amb Ω) f := by
  have h := hu ⟨cutoffMul (isTestFn_mul hζ hζ) (u : H1amb Ω),
    cutoffMul_mem_H01 (isTestFn_mul hζ hζ) u.2⟩
  rw [Op.fullBilin_apply, EllipticCoeff.bilin_apply, Op.lowerBilin_apply] at h
  unfold TestedIdentity
  linarith only [h]

/-- **Energy identity for `ζ² U`.** Testing the weak formulation with `ζ² U` and bounding the
principal part from below by ellipticity gives
`λ ∑ᵢ ‖ζ Uᵢ‖² ≤ ⟪f, ζ² U₀⟫ - ∑ᵢ ⟪bᵢ (ζ Uᵢ), ζ U₀⟫ - ⟪c U₀, ζ² U₀⟫
  - ∑ᵢⱼ 2 ⟪aᵢⱼ (ζ Uᵢ), ∂ⱼζ U₀⟫`,
where `Uᵢ` are the gradient components of `U`. -/
lemma caccioppoli_lower_bound (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (U : H1amb Ω) (f : L2D Ω)
    (hid : TestedIdentity Op hζ U f) :
    Op.lam * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2
      ≤ ⟪f, mulTest (isTestFn_mul hζ hζ) (U 0)⟫
        - ∑ i : Fin d, ⟪Op.bAct i (mulTest hζ (U i.succ)), mulTest hζ (U 0)⟫
        - ⟪Op.cAct (U 0), mulTest (isTestFn_mul hζ hζ) (U 0)⟫
        - ∑ i : Fin d, ∑ j : Fin d, 2 * ⟪Op.toEllipticCoeff.actL i j
            (mulTest hζ (U i.succ)), mulTestPartial hζ j (U 0)⟫ := by
  classical
  set A := Op.toEllipticCoeff with hA
  have hen := energy_ge A (fun i => mulTest hζ (U i.succ))
  have hbil : (∑ i, ∑ j, ⟪A.actL i j (U i.succ), cutoffMul (isTestFn_mul hζ hζ) U j.succ⟫)
      = (∑ i, ∑ j, ⟪A.actL i j (mulTest hζ (U i.succ)), mulTest hζ (U j.succ)⟫)
        + ∑ i, ∑ j, 2 * ⟪A.actL i j (mulTest hζ (U i.succ)), mulTestPartial hζ j (U 0)⟫ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cutoffMulOn_apply_succ, inner_add_right, ← actL_mulTest_regroup A hζ,
      ← actL_cross_regroup A hζ]
  have hlow : (∑ i, ⟪Op.bAct i (U i.succ), cutoffMul (isTestFn_mul hζ hζ) U 0⟫)
        + ⟪Op.cAct (U 0), cutoffMul (isTestFn_mul hζ hζ) U 0⟫
      = (∑ i, ⟪Op.bAct i (mulTest hζ (U i.succ)), mulTest hζ (U 0)⟫)
        + ⟪Op.cAct (U 0), mulTest (isTestFn_mul hζ hζ) (U 0)⟫ := by
    rw [cutoffMulOn_apply_zero]
    simp only [bAct_transport_regroup Op hζ]
  unfold TestedIdentity at hid
  rw [cutoffMulOn_apply_zero, ← inner_eq_setIntegral] at hid
  rw [cutoffMulOn_apply_zero] at hlow
  linarith only [hen, hid, hbil, hlow]

/-- **Interior energy estimate for a tested identity.** If `U ∈ H¹` satisfies the weak identity
against `ζ² U` (`TestedIdentity`), the cutoff-weighted gradient energy `(λ/2) ∑ᵢ ‖ζ Uᵢ‖²` is
bounded by `C (‖f‖² + ‖U₀‖²)`. The constant is quantified before `U` and `f`, so it depends only
on `λ`, `Λ`, `‖b‖∞`, `‖c‖∞`, `‖ζ‖∞` and `‖∇ζ‖∞`. The ellipticity lower bound [`energy_ge`]
controls the principal part from below, and Cauchy-Schwarz together with the Peter-Paul
inequality absorbs the cross, transport, zeroth-order and right-hand terms. -/
theorem caccioppoli_core (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), TestedIdentity Op hζ U f →
      Op.lam / 2 * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖U 0‖ ^ 2) := by
  classical
  set A := Op.toEllipticCoeff with hA
  have hZ := hζ.supNorm_nonneg
  have hZ2 := (isTestFn_mul hζ hζ).supNorm_nonneg
  have hSW : 0 ≤ ∑ j : Fin d, hζ.partialSupNorm j :=
    Finset.sum_nonneg fun j _ => hζ.partialSupNorm_nonneg j
  have hΛ := A.Λ_nonneg
  have hlam := A.lam_pos
  set β : ℝ := (Op.Bsup * hζ.supNorm + 2 * A.Λ * ∑ j : Fin d, hζ.partialSupNorm j)
    * Real.sqrt d with hβ
  set K₂ : ℝ := (isTestFn_mul hζ hζ).supNorm * (1 + Op.Csup) with hK₂
  have hβ0 : 0 ≤ β := by have := Op.Bsup_nonneg; positivity
  have hK₂0 : 0 ≤ K₂ := by have := Op.Csup_nonneg; positivity
  refine ⟨2 * (β ^ 2 / (2 * A.lam) + K₂), by positivity, fun U f hid => ?_⟩
  have hlow := caccioppoli_lower_bound Op hζ U f hid
  set r : ℝ := ‖U 0‖ with hr
  set E : ℝ := ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2 with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ≤ Real.sqrt d * Real.sqrt E :=
    sum_le_sqrt_card_mul_sqrt_sum_sq _
  have hS0 : 0 ≤ ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hζu0 : ‖mulTest hζ (U 0)‖ ≤ hζ.supNorm * r := norm_mulTest_le_supNorm _ _
  have hζ2u0 : ‖mulTest (isTestFn_mul hζ hζ) (U 0)‖
      ≤ (isTestFn_mul hζ hζ).supNorm * r :=
    norm_mulTest_le_supNorm _ _
  have hT1 : ⟪f, mulTest (isTestFn_mul hζ hζ) (U 0)⟫
      ≤ (isTestFn_mul hζ hζ).supNorm * ‖f‖ * r :=
    (real_inner_le_norm _ _).trans (by nlinarith only [hζ2u0, norm_nonneg f])
  have hTb : -∑ i : Fin d, ⟪Op.bAct i (mulTest hζ (U i.succ)),
        mulTest hζ (U 0)⟫
      ≤ Op.Bsup * hζ.supNorm * r * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (neg_real_inner_le_mul_norm _ _).trans ?_
    calc _ ≤ (Op.Bsup * ‖mulTest hζ (U i.succ)‖) * (hζ.supNorm * r) :=
          mul_le_mul (Op.norm_bAct_le i _) hζu0 (norm_nonneg _)
            (mul_nonneg Op.Bsup_nonneg (norm_nonneg _))
      _ = _ := by ring
  have hTc : -⟪Op.cAct (U 0), mulTest (isTestFn_mul hζ hζ) (U 0)⟫
      ≤ Op.Csup * (isTestFn_mul hζ hζ).supNorm * r ^ 2 := by
    refine (neg_real_inner_le_mul_norm _ _).trans ?_
    calc _ ≤ (Op.Csup * r) * ((isTestFn_mul hζ hζ).supNorm * r) :=
          mul_le_mul (Op.norm_cAct_le _) hζ2u0 (norm_nonneg _)
            (mul_nonneg Op.Csup_nonneg (norm_nonneg _))
      _ = _ := by ring
  have hTx := neg_cross_sum_le A hζ (fun i => U i.succ) (U 0)
  have hkey : A.lam * Real.sqrt E ^ 2 ≤ β * (‖f‖ + r) * Real.sqrt E + K₂ * (‖f‖ + r) ^ 2 := by
    rw [Real.sq_sqrt hE0]
    have he := Real.sqrt_nonneg E
    have hr0 : 0 ≤ r := norm_nonneg _
    have hf0 := norm_nonneg f
    have h1 : (Op.Bsup * hζ.supNorm + 2 * A.Λ * ∑ j : Fin d, hζ.partialSupNorm j) * r
        * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ≤ β * (‖f‖ + r) * Real.sqrt E := by
      calc _ ≤ (Op.Bsup * hζ.supNorm + 2 * A.Λ * ∑ j : Fin d, hζ.partialSupNorm j) * r
              * (Real.sqrt d * Real.sqrt E) :=
            mul_le_mul_of_nonneg_left hS (by have := Op.Bsup_nonneg; positivity)
        _ = β * r * Real.sqrt E := by rw [hβ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hβ0) he
    have h2 : (isTestFn_mul hζ hζ).supNorm * ‖f‖ * r
        + Op.Csup * (isTestFn_mul hζ hζ).supNorm * r ^ 2 ≤ K₂ * (‖f‖ + r) ^ 2 := by
      rw [hK₂]
      have := Op.Csup_nonneg
      nlinarith only [mul_nonneg hZ2 (mul_nonneg hf0 hr0), mul_nonneg hZ2 (sq_nonneg ‖f‖),
        mul_nonneg hZ2 (sq_nonneg r), mul_nonneg (mul_nonneg hZ2 this) (sq_nonneg ‖f‖),
        mul_nonneg (mul_nonneg hZ2 this) (mul_nonneg hf0 hr0)]
    linarith only [hlow, hT1, hTb, hTc, hTx, h1, h2]
  have habs := absorb_energy hlam hkey
  rw [Real.sq_sqrt hE0] at habs
  have hN : (‖f‖ + r) ^ 2 ≤ 2 * (‖f‖ ^ 2 + r ^ 2) := by nlinarith only [sq_nonneg (‖f‖ - r)]
  have hC : 0 ≤ β ^ 2 / (2 * A.lam) + K₂ := by positivity
  calc _ ≤ _ := habs
    _ ≤ (β ^ 2 / (2 * A.lam) + K₂) * (2 * (‖f‖ ^ 2 + r ^ 2)) := mul_le_mul_of_nonneg_left hN hC
    _ = _ := by ring

/-- **Interior energy (Caccioppoli) estimate.** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` and a cutoff `ζ` (a test function), the cutoff-weighted gradient energy
`(λ/2) ∫_Ω ζ² |∇u|²` is bounded by `C · (‖f‖²_{L²} + ‖u₀‖²_{L²})`. The constant is quantified
before the solution and the datum, so it depends only on `λ`, `Λ`, `‖b‖∞`, `‖c‖∞`, `‖ζ‖∞`,
and `‖∇ζ‖∞`. Testing the weak formulation with
`ζ² u` (admissible by [`cutoffMul_mem_H01`]), the ellipticity lower bound [`energy_ge`]
controls the principal part from below, and Cauchy-Schwarz together with the Peter-Paul
(Young) inequality absorbs the cross, transport, zeroth-order, and right-hand terms into a
`(λ/2) ∫_Ω ζ² |∇u|²` share. Since `ζ ≡ 1` on an interior set `V`, this gives
`‖∇u‖_{L²(V)} ≤ C' (‖f‖ + ‖u₀‖)`. See Gilbarg-Trudinger, *Elliptic PDE of Second Order*,
Theorem 8.8, and Evans, *Partial Differential Equations* (2nd ed.), §6.3.1.

Guo, *Partial Differential Equations* (JHU AS.110.631-632), Lemma X.3.5 also has the name
Caccioppoli, and is a different statement: it takes a non-negative subsolution `Lv ≥ 0` of the
principal part alone and bounds `∫ |∇(φv)|²` by `‖∇φ‖²_∞ ∫ v²`, with no datum on the right. This
statement takes a solution of `Lu = f` for the full operator, has `f` on the right, and imposes
no sign condition, so neither implies the other. Gilbarg and Trudinger Theorem 8.8 remains the
match, cited here rather than transcribed. -/
theorem caccioppoli (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      Op.lam / 2 * ∑ i : Fin d, ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := caccioppoli_core Op hζ
  exact ⟨C, hC, fun u f hu => h _ f (testedIdentity_of_H01 Op hζ u f hu)⟩

end EllipticPdes.Regularity
