/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Extension.Basic
public import EllipticPdes.Sobolev.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Integration by parts against a `C¹` test function

`HasWeakGradOn` asks for the integration-by-parts identity against smooth test functions. The
extension operator needs it against a `C¹` one: a boundary chart of a `C¹` domain is `C¹`, so a
smooth test function pulled back through it is `C¹` and no better.

Mollification supplies the smooth test functions. The mollification of a `C¹` class of compact
support is smooth, its support sits in a closed thickening of the original, its partial
derivatives are the mollified partial derivatives, and both stay bounded by the suprema of the
originals while converging pointwise. Dominated convergence passes the identity.

## Main declarations

* `EllipticPdes.Extension.mollifier`: the family of bumps of radius `r / (n + 1)`.
* `EllipticPdes.Extension.norm_normed_convolution_le`: a mollification is bounded by the
  supremum of what it mollifies.
* `EllipticPdes.Extension.partialD_convolution_normed`: the partial derivative of a
  mollification is the mollification of the partial derivative.
* `EllipticPdes.Extension.hasWeakGradOn_contDiffOne`: the identity of a weak gradient, against
  a `C¹` test function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)

section Mollifier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- The `n`-th bump of the standard mollifying family of scale `r`, of outer radius
`r / (n + 1)`. -/
def mollifier (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := r / (n + 1) / 2
  rOut := r / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

omit [NormedSpace ℝ E] [HasContDiffBump E] in
/-- The outer radius of `mollifier r hr n` is `r / (n + 1)`. -/
@[simp] theorem rOut_mollifier (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (mollifier r hr n : ContDiffBump (0 : E)).rOut = r / (n + 1) := rfl

omit [NormedSpace ℝ E] [HasContDiffBump E] in
/-- The bumps of the standard mollifying family have outer radius at most `r`. -/
theorem rOut_mollifier_le (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (mollifier r hr n : ContDiffBump (0 : E)).rOut ≤ r := by
  rw [rOut_mollifier]
  exact div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

omit [NormedSpace ℝ E] [HasContDiffBump E] in
/-- The outer radii of the standard mollifying family tend to zero. -/
theorem tendsto_rOut_mollifier (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (mollifier r hr n : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **Bound on a mollification by what it mollifies.** The normed bump is a probability
density, so the convolution is an average and inherits the bound. -/
theorem norm_normed_convolution_le (ρ : ContDiffBump (0 : E)) {h : E → ℝ} (hc : Continuous h)
    {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M) (x : E) : ‖(ρ.normed μ ⋆[Lsm, μ] h) x‖ ≤ M := by
  have hex : ConvolutionExistsAt (ρ.normed μ) h x Lsm μ :=
    ρ.hasCompactSupport_normed.convolutionExists_left (L := Lsm)
      (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous hc.locallyIntegrable x
  rw [convolution_def]
  calc ‖∫ t, (Lsm (ρ.normed μ t)) (h (x - t)) ∂μ‖
      ≤ ∫ t, ‖(Lsm (ρ.normed μ t)) (h (x - t))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ρ.normed μ t * M ∂μ := by
        refine integral_mono hex.norm (ρ.integrable_normed.mul_const M) fun t => ?_
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (ρ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hM _) (ρ.nonneg_normed t)
    _ = M := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- **Support of a mollification.** The mollification of a class of compact support is
supported in the closed thickening of that support by the radius of the bump. -/
theorem tsupport_normed_convolution_subset (ρ : ContDiffBump (0 : E)) {ψ : E → ℝ}
    (hψ : HasCompactSupport ψ) :
    tsupport (ρ.normed μ ⋆[Lsm, μ] ψ) ⊆ cthickening ρ.rOut (tsupport ψ) := by
  refine closure_minimal ?_ isClosed_cthickening
  rw [← hψ.isCompact.closedBall_zero_add ρ.rOut_pos.le]
  refine (support_convolution_subset Lsm).trans (Set.add_subset_add ?_ (subset_tsupport ψ))
  rw [ρ.support_normed_eq]
  exact ball_subset_closedBall

end Mollifier

/-- **Partial derivative of a mollification.** For `ψ` of class `C¹` with compact support,
`ρ ⋆ ψ` is differentiable and its partial derivatives are the mollified partial derivatives. -/
theorem partialD_convolution_normed (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (ρ.normed volume ⋆[Lsm, volume] ψ) x
      = (ρ.normed volume ⋆[Lsm, volume] (partialD k ψ)) x := by
  have hρli : LocallyIntegrable (ρ.normed volume) volume :=
    (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous.locallyIntegrable
  have hfd := hψcs.hasFDerivAt_convolution_right (L := Lsm) hρli hψ x
  rw [partialD, hfd.fderiv,
    convolution_precompR_apply Lsm hρli (hψcs.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) x
      (EuclideanSpace.single k (1 : ℝ))]
  rfl

/-- **Integration by parts against a `C¹` test function.** A weak gradient on an open set
satisfies its defining identity against every `C¹` function of compact support inside the set,
and not only against the smooth ones the definition names. -/
theorem hasWeakGradOn_contDiffOne {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ B) (k : Fin d) :
    ∫ x in B, u x * partialD k ψ x = - ∫ x in B, g k x * ψ x := by
  obtain ⟨ε, hε, hsub⟩ := hψcs.isCompact.exists_cthickening_subset_open hBopen hψs
  have hdcs : HasCompactSupport (partialD k ψ) := hψcs.partialD k
  have hdc : Continuous (partialD k ψ) := hψ.continuous_partialD one_ne_zero k
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨N, hN⟩ := hdcs.exists_bound_of_continuous hdc
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    fun n => mollifier ε hε n with hρ
  set ψn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => (ρ n).normed volume ⋆[Lsm, volume] ψ with hψn
  have hsm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (L := Lsm) (ρ n).contDiff_normed
      hψ.continuous.locallyIntegrable
  have hrOut := tendsto_rOut_mollifier (E := EuclideanSpace ℝ (Fin d)) ε hε
  refine integral_eq_neg_integral_of_tendsto hBopen.measurableSet hu (hgi k)
    (F := fun n => partialD k (ψn n)) (G := ψn) (fun n => (hsm n).continuous_partialD (by simp) k)
    (fun n => (hsm n).continuous) (N := N) (P := M)
    (fun n x => ?_) (fun n x => norm_normed_convolution_le (ρ n) hψ.continuous hM x)
    (fun x _ => ?_) (fun x _ => ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) hrOut hψ.continuous x) (fun n => ?_)
  · rw [partialD_convolution_normed (ρ n) hψ hψcs k x]
    exact norm_normed_convolution_le (ρ n) hdc hN x
  · exact (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := ρ)
      hrOut hdc x).congr fun n => (partialD_convolution_normed (ρ n) hψ hψcs k x).symm
  · refine hwg (ψn n) (hsm n) (HasCompactSupport.convolution (L := Lsm)
      (ρ n).hasCompactSupport_normed hψcs) ((tsupport_normed_convolution_subset (ρ n) hψcs).trans
      (fun x hx => hsub (cthickening_mono (rOut_mollifier_le ε hε n) _ hx))) k

end EllipticPdes.Extension
