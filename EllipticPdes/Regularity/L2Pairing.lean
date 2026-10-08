/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.MulIterated

/-!
# Pairing an `L²` class against a test function

Evans's step 3 of §6.3.1, Theorem 2 assembles a datum out of a dozen products of a coefficient
against a derivative of the solution, and every one of them reaches the statement as an integral
against a test function. Moving between the sum of the integrals and the integral of the sum is
all of the bookkeeping, the same three facts each time: the pairing is additive, it
commutes with a finite sum, and a weighted class pairs as the weight times the class.

Integrability is what makes the moves legal, and it is uniform: an `L²` class against a
continuous compactly supported function is integrable, by Hölder. Every lemma here takes the
test function as smooth with compact support and asks nothing about its support, since none of
these steps localises.

## Main declarations

* `pairTest`: the pairing against a test function as a continuous linear functional on `L²(V)`.
* `setIntegral_add_mul_testFn`, `setIntegral_sub_mul_testFn`, `setIntegral_neg_mul_testFn`:
  the pairing is additive.
* `setIntegral_finsetSum_mul_testFn`, `setIntegral_sum_mul_testFn`: the pairing commutes with a
  finite sum.
* `setIntegral_mulL2_mul_testFn`: a weighted class pairs as the weight against the class.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}

/-- **The pairing against a test function as a continuous linear functional.**
`F ↦ ∫_V F φ` is the inner product against the class of `φ`, so additivity, subtraction and
finite sums are the linearity of a functional. -/
def pairTest {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) : L2D V →L[ℝ] ℝ :=
  innerSL ℝ (((hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict
    V).toLp φ)

/-- `pairTest hφc hφcs F` is the integral `∫_V F φ`. -/
theorem pairTest_apply {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (F : L2D V) :
    pairTest hφc hφcs F = ∫ x in V, (F x : ℝ) * φ x := by
  rw [pairTest, innerSL_apply_apply,
    inner_Lp_eq_integral_of_ae (MemLp.coeFn_toLp _) Filter.EventuallyEq.rfl]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The pairing is additive in the class. -/
theorem setIntegral_add_mul_testFn (F G : L2D V) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((F + G) x : ℝ) * φ x)
      = (∫ x in V, (F x : ℝ) * φ x) + ∫ x in V, (G x : ℝ) * φ x := by
  simpa only [pairTest_apply] using (pairTest hφc hφcs).map_add F G

/-- The pairing subtracts in the class. -/
theorem setIntegral_sub_mul_testFn (F G : L2D V) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((F - G) x : ℝ) * φ x)
      = (∫ x in V, (F x : ℝ) * φ x) - ∫ x in V, (G x : ℝ) * φ x := by
  simpa only [pairTest_apply] using (pairTest hφc hφcs).map_sub F G

/-- The pairing negates in the class. -/
theorem setIntegral_neg_mul_testFn (F : L2D V) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in V, ((-F) x : ℝ) * φ x) = -∫ x in V, (F x : ℝ) * φ x := by
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg F] with x hx
  rw [hx, Pi.neg_apply, neg_mul]

/-- The pairing commutes with a finite sum over a `Finset`. -/
theorem setIntegral_finsetSum_mul_testFn {ι : Type*} (s : Finset ι) (F : ι → L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((∑ i ∈ s, F i) x : ℝ) * φ x) = ∑ i ∈ s, ∫ x in V, (F i x : ℝ) * φ x := by
  simpa only [pairTest_apply] using map_sum (pairTest hφc hφcs) F s

/-- The pairing commutes with a finite sum over a `Fintype`. -/
theorem setIntegral_sum_mul_testFn {ι : Type*} [Fintype ι] (F : ι → L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((∑ i, F i) x : ℝ) * φ x) = ∑ i, ∫ x in V, (F i x : ℝ) * φ x :=
  setIntegral_finsetSum_mul_testFn Finset.univ F hφc hφcs

/-- **Pairing of an extension by zero over its original set.** A whole-space integral of a
weight against the extension of an `L²(S)` class collapses to an integral over `S`. Stated with
a weight on each side, which is the shape every block of the bilinear form takes. -/
theorem integral_extendL2_mul_mul (hVm : MeasurableSet V) (F : L2D V)
    (a b : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x, a x * (extendL2 hVm F x : ℝ) * b x) = ∫ x in V, a x * (F x : ℝ) * b x := by
  have hae : (fun x => a x * (extendL2 hVm F x : ℝ) * b x)
      =ᵐ[volume] Set.indicator V (fun x => a x * (F x : ℝ) * b x) := by
    filter_upwards [coeFn_extendL2 hVm F] with x hx
    rw [hx]
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem hxV]
    · rw [Set.indicator_of_notMem hxV, Set.indicator_of_notMem hxV, mul_zero, zero_mul]
  rw [integral_congr_ae hae, integral_indicator hVm]

/-- **Splitting off a derivative of the test function by a cutoff.** Writing `χ ∂ⱼv` as
`∂ⱼ(χv) - (∂ⱼχ)v` moves the pairing onto the cut-off test function, which is the form the
differentiated equation is stated against. -/
theorem setIntegral_mul_cutoff_partialD_split (P : L2D V) {χ v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ) (hvc : ContDiff ℝ (⊤ : ℕ∞) v)
    (j : Fin d) :
    (∫ x in V, (P x : ℝ) * (χ x * partialD j v x))
      = (∫ x in V, (P x : ℝ) * partialD j (fun y => χ y * v y) x)
        - ∫ x in V, (P x : ℝ) * (partialD j χ x * v x) := by
  have hχd : Differentiable ℝ χ := hχc.differentiable (by simp)
  have hvd : Differentiable ℝ v := hvc.differentiable (by simp)
  have hi1 : Integrable (fun x => (P x : ℝ) * (χ x * partialD j v x)) (volume.restrict V) :=
    integrable_mul_testFn P (hχc.mul (contDiff_partialD hvc j)) hχcs.mul_right
  have hi2 : Integrable (fun x => (P x : ℝ) * (partialD j χ x * v x)) (volume.restrict V) :=
    integrable_mul_testFn P ((contDiff_partialD hχc j).mul hvc)
      (hχcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)).mul_right
  have hmid : (∫ x in V, (P x : ℝ) * partialD j (fun y => χ y * v y) x)
      = (∫ x in V, (P x : ℝ) * (χ x * partialD j v x))
        + ∫ x in V, (P x : ℝ) * (partialD j χ x * v x) := by
    rw [partialD_mul hχd hvd j, ← integral_add hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  linarith [hmid]

/-- **Two classes agreeing under a cutoff pair identically against anything the cutoff fixes.**
Where `θ·X = θ·Y` almost everywhere and `θψ = ψ` pointwise, the pairings against `ψ` agree, with
a weight in front, which is the shape every block of the bilinear form takes. This is how an
identification valid only after a cutoff is used: every weight the datum assembly pairs against
is supported where the outer cutoff of the tower is identically `1`. -/
theorem setIntegral_weight_mul_congr_of_cutoff_ae {θ : EuclideanSpace ℝ (Fin d) → ℝ}
    {X Y : L2D V}
    (h : (fun x => θ x * (X x : ℝ)) =ᵐ[volume.restrict V] fun x => θ x * (Y x : ℝ))
    (a : EuclideanSpace ℝ (Fin d) → ℝ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ∀ x, θ x * ψ x = ψ x) :
    (∫ x in V, a x * (X x : ℝ) * ψ x) = ∫ x in V, a x * (Y x : ℝ) * ψ x := by
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  have e : ∀ z : ℝ, a x * (θ x * z) * ψ x = a x * z * ψ x := by
    intro z
    conv_rhs => rw [← hψ x]
    ring
  rw [← e (X x : ℝ), hx, e (Y x : ℝ)]

/-- **Sum of two weighted classes paired against a cut-off test function.** The
differentiated equation groups its datum two terms at a time, one with a derivative of a
coefficient and one with a derivative of the solution, and the datum of the induction step names
them separately. This is the split, with the cutoff moved to the front where the datum has it. -/
theorem setIntegral_add_weight_mul_cutoff {a₁ a₂ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h₁m : Measurable a₁) {M₁ : ℝ}
    (h₁b : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a₁ x| ≤ M₁)
    (h₂m : Measurable a₂) {M₂ : ℝ}
    (h₂b : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a₂ x| ≤ M₂)
    (p₁ p₂ : L2D V) {ξ v : EuclideanSpace ℝ (Fin d) → ℝ} (hξc : ContDiff ℝ (⊤ : ℕ∞) ξ)
    (hξcs : HasCompactSupport ξ) (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ x in V, (a₁ x * (p₁ x : ℝ) + a₂ x * (p₂ x : ℝ)) * (ξ x * v x))
      = (∫ x in V, ξ x * (a₁ x * (p₁ x : ℝ)) * v x)
        + ∫ x in V, ξ x * (a₂ x * (p₂ x : ℝ)) * v x := by
  have hi₁ : Integrable (fun x => ξ x * (a₁ x * (p₁ x : ℝ)) * v x) (volume.restrict V) := by
    refine (integrable_mul_testFn (mulL2 h₁m h₁b p₁) (hξc.mul hvc) hξcs.mul_right).congr ?_
    filter_upwards [mulL2_coeFn h₁m h₁b p₁] with x hx
    rw [hx]
    ring
  have hi₂ : Integrable (fun x => ξ x * (a₂ x * (p₂ x : ℝ)) * v x) (volume.restrict V) := by
    refine (integrable_mul_testFn (mulL2 h₂m h₂b p₂) (hξc.mul hvc) hξcs.mul_right).congr ?_
    filter_upwards [mulL2_coeFn h₂m h₂b p₂] with x hx
    rw [hx]
    ring
  rw [← integral_add hi₁ hi₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- A weighted class pairs as the weight against the class. -/
theorem setIntegral_mulL2_mul_testFn {a : EuclideanSpace ℝ (Fin d) → ℝ} (ham : Measurable a)
    {M : ℝ} (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M) (p : L2D V)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in V, (mulL2 ham haM p x : ℝ) * φ x) = ∫ x in V, a x * (p x : ℝ) * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn ham haM p] with x hx
  rw [hx]

end EllipticPdes.Regularity
