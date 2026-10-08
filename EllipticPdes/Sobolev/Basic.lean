/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# H¹ and H₀¹ as weak-derivative Hilbert spaces

We realise `W^{1,2}(Ω)` as the **graph of the weak-gradient operator** inside the Hilbert space
`L²(Ω) × (L²(Ω))ᵈ` (encoded as `PiLp 2` over `Fin (d+1)`: coordinate `0` is the function,
coordinate `i.succ` the `i`-th weak partial). The weak-gradient relation is orthogonality to a
family of explicit "constraint vectors", so `W^{1,2}` is an orthogonal complement: closed,
complete, and a real Hilbert space with no further work.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal Distributions

noncomputable section

namespace MeasureTheory.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The real `L²` inner product of two classes is the integral of the product of their
representatives. -/
lemma real_inner_eq_integral (f g : Lp ℝ 2 μ) : ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ => Real.inner_apply _ _)

/-- The squared `L²` norm of a real class is the integral of the square of a representative. -/
lemma norm_sq_eq_integral_sq (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_integral]
  simp_rw [pow_two]

/-- The product of two real `L²` classes is integrable. -/
lemma integrable_mul (f g : Lp ℝ 2 μ) : Integrable (fun x => f x * g x) μ :=
  (L2.integrable_inner f g).congr (Filter.Eventually.of_forall fun _ => Real.inner_apply _ _)

/-- The square of a real `L²` class is integrable. -/
lemma integrable_sq (f : Lp ℝ 2 μ) : Integrable (fun x => f x ^ 2) μ :=
  (integrable_mul f f).congr (Filter.Eventually.of_forall fun _ => (pow_two _).symm)

end MeasureTheory.L2

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The real `L²` space on a domain `Ω ⊆ ℝ^d` (restricted Lebesgue measure). -/
abbrev L2D (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp ℝ 2 (volume.restrict Ω)

/-- Ambient Hilbert space for the graph encoding: a function value together with `d` gradient
components, with the ℓ² (H¹) inner product. Coordinate `0` is the function; coordinate `i.succ`
is the `i`-th weak partial derivative. -/
abbrev H1amb (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  PiLp 2 (fun _ : Fin (d + 1) => L2D Ω)

namespace H1amb

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function component of an ambient vector (coordinate `0`). -/
def fn (U : H1amb Ω) : L2D Ω := U 0

/-- The `i`-th gradient component of an ambient vector (coordinate `i.succ`). -/
def grad (U : H1amb Ω) (i : Fin d) : L2D Ω := U i.succ

/-- The function component is coordinate `0`. -/
lemma fn_def (U : H1amb Ω) : U.fn = U 0 := rfl

/-- The `i`-th gradient component is coordinate `i.succ`. -/
lemma grad_def (U : H1amb Ω) (i : Fin d) : U.grad i = U i.succ := rfl

/-- The `H¹` norm splits into the function part and the gradient part. -/
lemma norm_sq_eq (U : H1amb Ω) : ‖U‖ ^ 2 = ‖U.fn‖ ^ 2 + ∑ i, ‖U.grad i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

/-- The function part is bounded by the `H¹` norm. -/
lemma norm_fn_le (U : H1amb Ω) : ‖U.fn‖ ≤ ‖U‖ := PiLp.norm_apply_le U 0

/-- Each gradient component is bounded by the `H¹` norm. -/
lemma norm_grad_le (U : H1amb Ω) (i : Fin d) : ‖U.grad i‖ ≤ ‖U‖ := PiLp.norm_apply_le U i.succ

/-- The `H¹` inner product is the sum of the `L²` inner products of the function parts and of
the gradient components. -/
lemma inner_eq (U V : H1amb Ω) : ⟪U, V⟫ = ⟪U.fn, V.fn⟫ + ∑ i, ⟪U.grad i, V.grad i⟫ := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  rfl

end H1amb

/-- Inner product of a single-coordinate vector against an ambient vector picks out the
coordinate: `⟪single j a, U⟫ = ⟪a, U j⟫`. -/
lemma inner_single_left {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (j : Fin (d + 1)) (a : L2D Ω) (U : H1amb Ω) :
    ⟪PiLp.single 2 j a, U⟫ = ⟪a, U j⟫ := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro b _ hb
    rw [PiLp.single_eq_of_ne (p := 2) hb]
    simp
  · simp

/-! ### Test functions and their `L²` classes -/

/-- The `i`-th classical partial derivative of `φ` (a directional `fderiv`). -/
def partialD (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)

/-- The `i`-th partial derivative at a point is the `fderiv` applied to the `i`-th basis
vector. -/
lemma partialD_apply (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i φ x = fderiv ℝ φ x (EuclideanSpace.single i 1) := rfl

/-- At a point of differentiability the `i`-th partial derivative is the line derivative along
the `i`-th basis vector. -/
lemma partialD_eq_lineDeriv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hφ : DifferentiableAt ℝ φ x) (i : Fin d) :
    partialD i φ x = lineDeriv ℝ φ x (EuclideanSpace.single i 1) :=
  hφ.lineDeriv_eq_fderiv.symm

/-- `partialD` is additive on differentiable functions. -/
lemma partialD_add {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (i : Fin d) :
    partialD i (φ + ψ) = partialD i φ + partialD i ψ := by
  funext x
  simp only [partialD, Pi.add_apply]
  rw [fderiv_add (hφ x) (hψ x), _root_.add_apply]

/-- `partialD` commutes with scalar multiplication on differentiable functions. -/
lemma partialD_const_smul {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (c : ℝ) (i : Fin d) :
    partialD i (c • φ) = c • partialD i φ := by
  funext x
  simp only [partialD, Pi.smul_apply]
  rw [fderiv_const_smul (hφ x) c, _root_.smul_apply]

/-- The classical partial of the zero function is zero. -/
lemma partialD_zero (i : Fin d) :
    partialD i (0 : EuclideanSpace ℝ (Fin d) → ℝ) = 0 := by
  funext x; simp [partialD]

/-- The topological support of a partial derivative sits inside the support of the
function: off `tsupport φ` the function is locally zero, so `fderiv` vanishes. -/
lemma tsupport_partialD_subset (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    tsupport (partialD i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) (EuclideanSpace.single i 1)

/-- A smooth, compactly supported test function whose support sits inside `Ω`. -/
def IsTestFn (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

namespace IsTestFn

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A test function is smooth. -/
lemma contDiff (h : IsTestFn Ω φ) : ContDiff ℝ (⊤ : ℕ∞) φ := h.1

/-- A test function has compact support. -/
lemma hasCompactSupport (h : IsTestFn Ω φ) : HasCompactSupport φ := h.2.1

/-- The support of a test function lies in the domain. -/
lemma tsupport_subset (h : IsTestFn Ω φ) : tsupport φ ⊆ Ω := h.2.2

/-- A test function is differentiable. -/
lemma differentiable (h : IsTestFn Ω φ) : Differentiable ℝ φ := h.1.differentiable (by simp)

/-- A test function is continuous. -/
lemma continuous (h : IsTestFn Ω φ) : Continuous φ := h.1.continuous

/-- Test functions are monotone in the domain: a test function of `Ω` is a test
function of any superset. -/
lemma mono {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hsub : Ω ⊆ Ω')
    (h : IsTestFn Ω φ) : IsTestFn Ω' φ :=
  ⟨h.1, h.2.1, h.2.2.trans hsub⟩

/-- Each partial derivative of a test function is continuous. -/
lemma continuous_partialD (h : IsTestFn Ω φ) (i : Fin d) : Continuous (partialD i φ) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Each partial derivative of a test function has compact support. -/
lemma hasCompactSupport_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    HasCompactSupport (partialD i φ) := by
  exact h.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)

/-- `φ` being a test function is preserved under sums. -/
lemma add (h : IsTestFn Ω φ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (h' : IsTestFn Ω ψ) :
    IsTestFn Ω (φ + ψ) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, by
    refine Set.Subset.trans ?_ (Set.union_subset h.2.2 h'.2.2)
    refine (closure_mono (Function.support_add φ ψ)).trans ?_
    rw [closure_union]
    exact subset_rfl⟩

/-- `φ` being a test function is preserved under scalar multiplication. -/
lemma const_smul (h : IsTestFn Ω φ) (c : ℝ) : IsTestFn Ω (c • φ) :=
  ⟨h.1.const_smul c,
    h.2.1.of_isClosed_subset isClosed_closure (tsupport_smul_subset_right (fun _ => c) φ),
    (tsupport_smul_subset_right (fun _ => c) φ).trans h.2.2⟩

/-- The zero function is a test function. -/
lemma zero : IsTestFn Ω (0 : EuclideanSpace ℝ (Fin d) → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩

/-- A test function lies in `L²(Ω)`. -/
lemma memLp (h : IsTestFn Ω φ) : MemLp φ 2 (volume.restrict Ω) :=
  h.continuous.memLp_of_hasCompactSupport h.2.1

alias mem_lp := memLp

/-- Each partial derivative of a test function lies in `L²(Ω)`. -/
lemma memLp_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    MemLp (partialD i φ) 2 (volume.restrict Ω) :=
  (h.continuous_partialD i).memLp_of_hasCompactSupport (h.hasCompactSupport_partialD i)

/-- The `L²(Ω)` class of a test function. -/
def testCls (h : IsTestFn Ω φ) : L2D Ω := h.memLp.toLp φ

/-- The `L²(Ω)` class of the `i`-th partial derivative of a test function. -/
def partialCls (h : IsTestFn Ω φ) (i : Fin d) : L2D Ω :=
  (h.memLp_partialD i).toLp (partialD i φ)

/-- A representative of `testCls` is the test function almost everywhere. -/
@[simp] lemma coeFn_testCls (h : IsTestFn Ω φ) : ⇑h.testCls =ᵐ[volume.restrict Ω] φ :=
  h.memLp.coeFn_toLp

/-- A representative of `partialCls` is the classical partial derivative almost everywhere. -/
@[simp] lemma coeFn_partialCls (h : IsTestFn Ω φ) (i : Fin d) :
    ⇑(h.partialCls i) =ᵐ[volume.restrict Ω] partialD i φ :=
  (h.memLp_partialD i).coeFn_toLp

/-- Constraint vector: orthogonality to it expresses one instance of the weak-gradient
relation `⟪U₀, [∂ᵢφ]⟫ + ⟪U_{i+1}, [φ]⟫ = 0` (coordinate `0` is the function, coordinate
`i.succ` the `i`-th weak partial). -/
def constraintVec (h : IsTestFn Ω φ) (i : Fin d) : H1amb Ω :=
  PiLp.single 2 0 (h.partialCls i) + PiLp.single 2 i.succ h.testCls

/-- Pairing a constraint vector against `U` extracts the weak-gradient relation. -/
lemma inner_constraintVec (h : IsTestFn Ω φ) (i : Fin d) (U : H1amb Ω) :
    ⟪h.constraintVec i, U⟫ = ⟪h.partialCls i, U 0⟫ + ⟪h.testCls, U i.succ⟫ := by
  rw [constraintVec, inner_add_left, inner_single_left, inner_single_left]

/-- A test function embedded as its graph `(φ, ∇φ)` in the ambient space: coordinate `0`
is the function, coordinate `i.succ` its `i`-th classical (= weak) partial. -/
def testGraph (h : IsTestFn Ω φ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons h.testCls (fun i => h.partialCls i))

/-- Simp lemma: `testGraph h 0 = testCls h`. -/
@[simp] lemma testGraph_zero (h : IsTestFn Ω φ) : h.testGraph 0 = h.testCls := by
  rw [testGraph, PiLp.toLp_apply, Fin.cons_zero]

/-- Simp lemma: `testGraph h i.succ = partialCls h i`. -/
@[simp] lemma testGraph_succ (h : IsTestFn Ω φ) (i : Fin d) :
    h.testGraph i.succ = h.partialCls i := by
  rw [testGraph, PiLp.toLp_apply, Fin.cons_succ]

/-- The graph embedding is additive: `(φ + ψ)` graphs to the sum of the graphs. -/
lemma testGraph_add (h : IsTestFn Ω φ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h' : IsTestFn Ω ψ) :
    h.testGraph + h'.testGraph = (h.add h').testGraph := by
  apply PiLp.ext
  intro j
  rw [PiLp.add_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls]
    rw [← MemLp.toLp_add]
  · simp only [testGraph_succ, partialCls]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq
      (partialD_add (h.1.differentiable (by simp)) (h'.1.differentiable (by simp)) i).symm)

/-- The graph embedding commutes with scalar multiplication. -/
lemma testGraph_const_smul (h : IsTestFn Ω φ) (c : ℝ) :
    c • h.testGraph = (h.const_smul c).testGraph := by
  apply PiLp.ext
  intro j
  rw [PiLp.smul_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls]
    rw [← MemLp.toLp_const_smul]
  · simp only [testGraph_succ, partialCls]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq
      (partialD_const_smul (h.1.differentiable (by simp)) c i).symm)

/-- The graph of the zero function is the zero vector. -/
lemma testGraph_zero_fn : (IsTestFn.zero (Ω := Ω)).testGraph = 0 := by
  apply PiLp.ext
  intro j
  rw [PiLp.zero_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls, MemLp.toLp_zero]
  · simp only [testGraph_succ, partialCls]
    rw [MemLp.toLp_congr (IsTestFn.zero.memLp_partialD i) MemLp.zero
        (Filter.EventuallyEq.of_eq (partialD_zero i)), MemLp.toLp_zero]

/-- A test function of an open set is a Mathlib test function `𝓓(Ω, ℝ)`. -/
def toTestFunction {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (h : IsTestFn Ω φ) : 𝓓((⟨Ω, hΩ⟩ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))), ℝ) :=
  ⟨φ, h.contDiff, h.hasCompactSupport, h.tsupport_subset⟩

/-- The function of `toTestFunction` is the test function itself. -/
@[simp] lemma coe_toTestFunction {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (h : IsTestFn Ω φ) : ⇑(h.toTestFunction hΩ) = φ := rfl

end IsTestFn

/-- For an open set, `IsTestFn` is the predicate of being (the function of) a Mathlib test
function `𝓓(Ω, ℝ)`. -/
lemma isTestFn_iff_testFunction {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsTestFn Ω φ ↔ ∃ ψ : 𝓓((⟨Ω, hΩ⟩ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))), ℝ),
      ⇑ψ = φ :=
  ⟨fun h => ⟨h.toTestFunction hΩ, rfl⟩, by
    rintro ⟨ψ, rfl⟩
    exact ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩⟩

/-- The real `L²(Ω)` inner product of two `MemLp.toLp` classes is the integral of the
product over `Ω`. -/
lemma inner_toLp_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω)) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x in Ω, f x * g x := by
  rw [L2.real_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
  rw [ha, hb]

/-! ### Weak-gradient graph space `W^{1,2}(Ω)` -/

/-- The set of all constraint vectors over `Ω`. -/
def constraintSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { w | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ) (i : Fin d),
      w = h.constraintVec i }

/-- `W^{1,2}(Ω)`: functions paired with their weak `L²` gradient, realised as the
orthogonal complement of the constraint vectors inside the ambient Hilbert space. As an
orthogonal complement it is automatically a closed, complete, real Hilbert space. -/
def W12 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (constraintSet Ω))ᗮ

/-- `W^{1,2}(Ω)` is complete, being an orthogonal complement in a Hilbert space. -/
instance instCompleteSpaceW12 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (W12 Ω) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℝ (constraintSet Ω))ᗮ)

namespace W12

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function component of an element of `W^{1,2}(Ω)`. -/
def fn (U : W12 Ω) : L2D Ω := H1amb.fn (U : H1amb Ω)

/-- The `i`-th weak partial derivative of an element of `W^{1,2}(Ω)`. -/
def grad (U : W12 Ω) (i : Fin d) : L2D Ω := H1amb.grad (U : H1amb Ω) i

/-- The function component is coordinate `0`. -/
lemma fn_def (U : W12 Ω) : fn U = (U : H1amb Ω) 0 := rfl

/-- The `i`-th weak partial derivative is coordinate `i.succ`. -/
lemma grad_def (U : W12 Ω) (i : Fin d) : grad U i = (U : H1amb Ω) i.succ := rfl

/-- The `W^{1,2}` norm splits into the function part and the gradient part. -/
lemma norm_sq_eq (U : W12 Ω) : ‖U‖ ^ 2 = ‖fn U‖ ^ 2 + ∑ i, ‖grad U i‖ ^ 2 :=
  H1amb.norm_sq_eq (U : H1amb Ω)

end W12

/-- Membership in `W^{1,2}(Ω)` is exactly the weak-gradient relation tested against every
test function: `⟪U₀, [∂ᵢφ]⟫ + ⟪U_{i+1}, [φ]⟫ = 0`. This is what makes an element of `W12`
a function (`U 0`) together with its weak `L²` gradient (`U ∘ Fin.succ`). -/
lemma mem_W12_iff {Ω : Set (EuclideanSpace ℝ (Fin d))} (U : H1amb Ω) :
    U ∈ W12 Ω ↔ ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ) (i : Fin d),
      ⟪h.partialCls i, U 0⟫ + ⟪h.testCls, U i.succ⟫ = 0 := by
  rw [W12, Submodule.mem_orthogonal]
  constructor
  · intro hU φ h i
    have hmem := hU (h.constraintVec i) (Submodule.subset_span ⟨φ, h, i, rfl⟩)
    rwa [h.inner_constraintVec] at hmem
  · intro hU u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨φ, h, i, rfl⟩ := hx
        rw [h.inner_constraintVec]; exact hU φ h i
    | zero => simp
    | add x y _ _ ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
    | smul c x _ ih => rw [inner_smul_left]; simp [ih]

/-! ### H₀¹(Ω) as the closure of the test functions -/

/-- The set of test-function graphs over `Ω`. -/
def testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { U | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ), U = h.testGraph }

/-- The test-function graphs already form a submodule: smooth compactly supported
functions are closed under sums and scalar multiples, and the graph embedding is linear.
This identifies `Submodule.span ℝ (testGraphSet Ω)` with `testGraphSet Ω` itself. -/
def testGraphSubmodule (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) where
  carrier := testGraphSet Ω
  add_mem' := by
    rintro _ _ ⟨φ, h, rfl⟩ ⟨ψ, h', rfl⟩
    exact ⟨φ + ψ, h.add h', h.testGraph_add h'⟩
  zero_mem' := ⟨0, IsTestFn.zero, IsTestFn.testGraph_zero_fn.symm⟩
  smul_mem' := by
    rintro c _ ⟨φ, h, rfl⟩
    exact ⟨c • φ, h.const_smul c, h.testGraph_const_smul c⟩

/-- The span of the test-function graphs equals the test-function graphs. -/
lemma span_testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule.span ℝ (testGraphSet Ω) = testGraphSubmodule Ω :=
  Submodule.span_eq (testGraphSubmodule Ω)

/-- `H₀¹(Ω) = W₀^{1,2}(Ω)`: the closure of the smooth compactly supported functions
inside the ambient `H¹` space. As a topological closure it is automatically a closed,
complete, real Hilbert space. -/
def H01 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure

/-- `H₀¹(Ω)` is complete, being a topological closure in a Hilbert space. -/
instance instCompleteSpaceH01 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (H01 Ω) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure)

/-- `H₀¹(Ω)` is the closure of the set of test-function graphs. -/
lemma coe_H01 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω : Set (H1amb Ω)) = closure (testGraphSet Ω) := by
  rw [H01, Submodule.topologicalClosure_coe, span_testGraphSet]
  rfl

/-- A closed set containing every test-function graph contains `H₀¹(Ω)`. -/
lemma H01_subset_of_isClosed {Ω : Set (EuclideanSpace ℝ (Fin d))} {S : Set (H1amb Ω)}
    (hS : IsClosed S) (h : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn Ω φ),
      hφ.testGraph ∈ S) :
    (H01 Ω : Set (H1amb Ω)) ⊆ S := by
  rw [coe_H01]
  exact closure_minimal (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ) hS

/-- A closed submodule containing every test-function graph contains `H₀¹(Ω)`. -/
lemma H01_le_of_isClosed {Ω : Set (EuclideanSpace ℝ (Fin d))} {S : Submodule ℝ (H1amb Ω)}
    (hS : IsClosed (S : Set (H1amb Ω)))
    (h : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn Ω φ), hφ.testGraph ∈ S) :
    H01 Ω ≤ S :=
  H01_subset_of_isClosed hS h

namespace H01

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function component of an element of `H₀¹(Ω)`. -/
def fn (U : H01 Ω) : L2D Ω := H1amb.fn (U : H1amb Ω)

/-- The `i`-th weak partial derivative of an element of `H₀¹(Ω)`. -/
def grad (U : H01 Ω) (i : Fin d) : L2D Ω := H1amb.grad (U : H1amb Ω) i

/-- The function component is coordinate `0`. -/
lemma fn_def (U : H01 Ω) : fn U = (U : H1amb Ω) 0 := rfl

/-- The `i`-th weak partial derivative is coordinate `i.succ`. -/
lemma grad_def (U : H01 Ω) (i : Fin d) : grad U i = (U : H1amb Ω) i.succ := rfl

/-- The `H₀¹` norm splits into the function part and the gradient part. -/
lemma norm_sq_eq (U : H01 Ω) : ‖U‖ ^ 2 = ‖fn U‖ ^ 2 + ∑ i, ‖grad U i‖ ^ 2 :=
  H1amb.norm_sq_eq (U : H1amb Ω)

end H01

/-- Integrability of a product where one factor is a continuous compactly supported map. -/
private lemma integrable_mul_of_compactSupport
    {u w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Continuous u) (hw : Continuous w) (hws : HasCompactSupport w) :
    Integrable (fun x => u x * w x) volume :=
  (hu.mul hw).integrable_of_hasCompactSupport (hws.mul_left)

/-- **Classical gradient of a test function as a weak gradient.** Hence every test
function's graph lies in `W^{1,2}(Ω)`. This is the integration-by-parts step (no boundary
term, by compact support). -/
lemma testGraph_mem_W12 {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    h.testGraph ∈ W12 Ω := by
  rw [mem_W12_iff]
  intro ψ g i
  simp only [IsTestFn.testGraph_zero, IsTestFn.testGraph_succ,
    IsTestFn.partialCls, IsTestFn.testCls]
  rw [inner_toLp_eq, inner_toLp_eq]
  -- Pass from `∫ … in Ω` to `∫ … ` over the whole space (both integrands vanish off `Ω`).
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (h.2.2 hc)), mul_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (g.2.2 hc)), zero_mul])]
  -- Integration by parts: `∫ ψ · ∂ᵢφ = - ∫ ∂ᵢψ · φ`, so the two terms cancel.
  simp only [partialD]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (integrable_mul_of_compactSupport (g.continuous_partialD i) h.continuous h.2.1)
        (integrable_mul_of_compactSupport g.continuous (h.continuous_partialD i)
          (h.hasCompactSupport_partialD i))
        (integrable_mul_of_compactSupport g.continuous h.continuous h.2.1)
        (fun x _ => (g.1.differentiable (by simp)).differentiableAt)
        (fun x _ => (h.1.differentiable (by simp)).differentiableAt)]
  rw [add_neg_cancel]

/-- `H₀¹(Ω) ⊆ W^{1,2}(Ω)`: every element of `H₀¹` is a function with a weak `L²` gradient.

Public because it is the bridge between the two solution spaces the library uses. The
interior regularity chain quantifies over `H01 Ω`, while Evans §6.3.1 Theorem 1 and
Fernández-Real and Ros-Oton both state the interior theory over the ambient Sobolev space,
so a generalisation of that chain runs through `W12 Ω` and needs this inclusion from outside
this file. -/
lemma H01_le_W12 (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω ≤ W12 Ω := by
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro U ⟨φ, h, rfl⟩
    exact testGraph_mem_W12 h
  · exact (Submodule.span ℝ (constraintSet Ω)).isClosed_orthogonal

end EllipticPdes.Sobolev
