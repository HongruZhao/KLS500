/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Common tools of the extension

The pairs of a class and a gradient that the extension operators act
on, with the seminorm that bounds them, and the small lemmas on supports, integrability and
seminorms that the files of the extension share.

## Main declarations

* `EllipticPdes.Extension.SobolevPair` and `EllipticPdes.Extension.pairNorm`: a class with its
  gradient, and the seminorm of both.
* `EllipticPdes.Extension.integral_eq_neg_integral_of_tendsto`: an integration by parts identity
  passes to a limit of bounded test functions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

/-- **Seminorm of a combination with coefficients of modulus at most one.** -/
theorem eLpNorm_sum_mul_le {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {p : ENNReal} (hp : 1 ≤ p) {a : ι → ℝ} (ha : ∀ i, |a i| ≤ 1) {w : ι → α → ℝ}
    (hw : ∀ i, AEStronglyMeasurable (w i) μ) :
    eLpNorm (fun y => ∑ i, a i * w i y) p μ ≤ ∑ i, eLpNorm (w i) p μ := by
  have hfun : (fun y => ∑ i, a i * w i y) = ∑ i, fun y => a i * w i y := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun]
  refine le_trans (eLpNorm_sum_le hp) (Finset.sum_le_sum fun i _ => ?_)
  refine eLpNorm_mono_ae ((hw i).const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs (a i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha i)

/-! ### Pairs of a class and a gradient -/

/-- A class together with a candidate for its gradient. This is the module the extension
operator acts on. -/
abbrev SobolevPair (d : ℕ) : Type :=
  (EuclideanSpace ℝ (Fin d) → ℝ) × (Fin d → EuclideanSpace ℝ (Fin d) → ℝ)

/-- The `Lᵖ` seminorm of a class plus those of the components of its gradient. -/
def pairNorm {d : ℕ} (p : ENNReal) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : ENNReal :=
  eLpNorm u p μ + ∑ i, eLpNorm (g i) p μ

section PairNorm

variable {d : ℕ} {p : ENNReal} {μ : Measure (EuclideanSpace ℝ (Fin d))}
  {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}

/-- The seminorm of the class is at most the pair seminorm. -/
theorem eLpNorm_le_pairNorm : eLpNorm u p μ ≤ pairNorm p μ u g := le_self_add

/-- The seminorm of one component of the gradient is at most the pair seminorm. -/
theorem eLpNorm_grad_le_pairNorm (k : Fin d) : eLpNorm (g k) p μ ≤ pairNorm p μ u g :=
  (Finset.single_le_sum (f := fun i => eLpNorm (g i) p μ) (fun _ _ => zero_le)
    (Finset.mem_univ k)).trans le_add_self

/-- The seminorm of the class and of one component of the gradient together is at most the pair
seminorm. -/
theorem eLpNorm_add_grad_le_pairNorm (k : Fin d) :
    eLpNorm u p μ + eLpNorm (g k) p μ ≤ pairNorm p μ u g :=
  add_le_add_right (Finset.single_le_sum (f := fun i => eLpNorm (g i) p μ)
    (fun _ _ => zero_le) (Finset.mem_univ k)) _

end PairNorm

/-- **Seminorm of a product with a bounded factor.** -/
theorem eLpNorm_mul_le_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f h : α → ℝ} {C : ℝ} {p : ENNReal} (hfh : AEStronglyMeasurable (fun x => f x * h x) μ)
    (hC : ∀ x, ‖h x‖ ≤ C) : eLpNorm (fun x => f x * h x) p μ ≤ ENNReal.ofReal C * eLpNorm f p μ :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfh (Filter.Eventually.of_forall fun x => by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)) p

/-! ### Supports and integrability -/

/-- **Chain rule for a partial derivative.** If `f` has derivative `L` at `x`, the `k`-th partial
derivative of `φ ∘ f` at `x` is the derivative of `φ` at `f x` along `L (eₖ)`. -/
theorem partialD_comp {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (hφ : DifferentiableAt ℝ φ (f x)) (hf : HasFDerivAt f L x)
    (k : Fin d) :
    partialD k (fun y => φ (f y)) x = fderiv ℝ φ (f x) (L (EuclideanSpace.single k (1 : ℝ))) := by
  have := (hφ.hasFDerivAt.comp x hf).fderiv
  rw [partialD, show (fun y => φ (f y)) = φ ∘ f from rfl, this]
  rfl

/-- **Dominated convergence for a product with a fixed integrable factor.** -/
theorem tendsto_setIntegral_mul {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {B : Set X} (hB : MeasurableSet B) {u : X → ℝ}
    (hu : IntegrableOn u B μ) {f : ℕ → X → ℝ} {f' : X → ℝ} (hf : ∀ n, Continuous (f n)) {C : ℝ}
    (hb : ∀ n x, ‖f n x‖ ≤ C) (hc : ∀ x ∈ B, Tendsto (fun n => f n x) atTop (𝓝 (f' x))) :
    Tendsto (fun n => ∫ x in B, u x * f n x ∂μ) atTop (𝓝 (∫ x in B, u x * f' x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => C * ‖u x‖)
    (fun n => hu.1.mul (hf n).aestronglyMeasurable) (hu.norm.const_mul C) (fun n => ?_)
    ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx => (hc x hx).const_mul (u x)))
  filter_upwards with x
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)

/-- **Passing an integration by parts identity to a limit.** If `∫_B u F n = -∫_B g G n` for
a sequence of continuous functions `F n`, `G n` that are uniformly bounded and converge
pointwise, then the identity holds for the limits. -/
theorem integral_eq_neg_integral_of_tendsto {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {B : Set X} (hB : MeasurableSet B) {u g : X → ℝ}
    (hu : IntegrableOn u B μ) (hg : IntegrableOn g B μ) {F G : ℕ → X → ℝ} {F' G' : X → ℝ}
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n)) {N P : ℝ}
    (hFb : ∀ n x, ‖F n x‖ ≤ N) (hGb : ∀ n x, ‖G n x‖ ≤ P)
    (hFc : ∀ x ∈ B, Tendsto (fun n => F n x) atTop (𝓝 (F' x)))
    (hGc : ∀ x ∈ B, Tendsto (fun n => G n x) atTop (𝓝 (G' x)))
    (hid : ∀ n, ∫ x in B, u x * F n x ∂μ = -∫ x in B, g x * G n x ∂μ) :
    ∫ x in B, u x * F' x ∂μ = -∫ x in B, g x * G' x ∂μ :=
  tendsto_nhds_unique (tendsto_setIntegral_mul hB hu hF hFb hFc)
    (by simpa only [hid] using (tendsto_setIntegral_mul hB hg hG hGb hGc).neg)

/-- The partial derivatives of a function of compact support have compact support. -/
theorem _root_.HasCompactSupport.partialD {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : HasCompactSupport ψ) (k : Fin d) : HasCompactSupport (partialD k ψ) :=
  hψ.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))

/-- The partial derivatives of a `C¹` function are continuous. -/
theorem _root_.ContDiff.continuous_partialD {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {n : WithTop ℕ∞} (hψ : ContDiff ℝ n ψ) (hn : n ≠ 0) (k : Fin d) : Continuous (partialD k ψ) :=
  (hψ.continuous_fderiv hn).clm_apply continuous_const

/-- **Determinant of the identity plus a rank-one map.** -/
theorem _root_.LinearMap.det_id_add_smulRight {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) (v : E) :
    (LinearMap.id + f.smulRight v).det = 1 + f v := by
  let b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (LinearMap.id + f.smulRight v)
      = 1 + Matrix.replicateCol Unit (b.repr v) * Matrix.replicateRow Unit (fun i => f (b i)) := by
    ext i k
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol,
      Matrix.replicateRow, Finsupp.single_apply, eq_comm, mul_comm]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h := congrArg f (b.sum_repr v)
  rw [map_sum] at h
  simpa [dotProduct, mul_comm] using h

/-- **One bound for a smooth compactly supported function and for each of its partials.** -/
theorem exists_bound_with_partials {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) h) (hcs : HasCompactSupport h) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y, ‖h y‖ ≤ C) ∧ ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k h y‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hcs.exists_bound_of_continuous hc.continuous
  choose Ck hCk using fun k => (hcs.partialD k).exists_bound_of_continuous
    (hc.continuous_partialD (by simp) k)
  have hsum0 : (0 : ℝ) ≤ ∑ k, Ck k := Finset.sum_nonneg fun k _ => (norm_nonneg _).trans (hCk k 0)
  have hC00 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0)
  refine ⟨C₀ + ∑ k, Ck k, by linarith, fun y => (hC₀ y).trans (by linarith),
    fun k y => (hCk k y).trans ?_⟩
  linarith [Finset.single_le_sum (f := fun j => Ck j)
    (fun j _ => (norm_nonneg _).trans (hCk j 0)) (Finset.mem_univ k)]

end EllipticPdes.Extension
