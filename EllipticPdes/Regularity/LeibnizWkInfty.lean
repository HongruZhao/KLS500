/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.MollifyWkInfty
public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.Caccioppoli

/-!
# Leibniz rule for a `W^{1,∞}` weight

This file proves the weak-derivative product rule for a weight in `W^{1,∞}`, which has no
classical derivative.

For a `C^∞` weight `b`, the product `b · φ` is a test function supported where `φ` is, so
`HasWeakDerivOn` applies to it directly and the classical Leibniz rule splits the result
(`weakDerivOn_smul_test_contDiff`). The mollification `a ⋆ ρ_ε` of a `W^{1,∞}` weight is
`C^∞`, and its derivative is the mollification of the weak derivative
(`partialD_convolution_eq_of_hasWeakPartial`), so the identity holds for every `ε`
(`weakDerivOn_mul_convolution_normed`). Each term then converges by dominated convergence:
`a ⋆ ρ_ε → a` almost everywhere by the Lebesgue differentiation theorem
(`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), and `|a ⋆ ρ_ε|` is at most the
essential bound of `a` (`abs_convolution_le_of_measurable`).

## Main declarations

* `weakDerivOn_smul_test_contDiff`: the identity for a `C^∞` weight, with no mollification.
* `tendsto_setIntegral_mul_convolution_of_measurable`: the mollification limit against an `L²`
  class, for a weight that is measurable and essentially bounded.
* `HasWeakDerivOn.mul_isWkInfty_left`: the Leibniz rule for a `W^{1,∞}` weight.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ENNReal Convolution

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A continuous compactly supported function is in `L²` of any restricted Lebesgue measure. -/
theorem memLp_two_restrict_of_continuous_hasCompactSupport
    {V : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) :
    MemLp h 2 (volume.restrict V) :=
  (hc.memLp_of_hasCompactSupport (μ := volume) hcs).restrict V

/-- An `L²(V)` class times a continuous compactly supported function is integrable on `V`. -/
theorem integrable_mul_of_continuous_hasCompactSupport {V : Set (EuclideanSpace ℝ (Fin d))}
    (u : Lp ℝ 2 (volume.restrict V)) {w : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous w)
    (hcs : HasCompactSupport w) : Integrable (fun x => (u x : ℝ) * w x) (volume.restrict V) := by
  exact (Lp.memLp u).integrable_mul (memLp_two_restrict_of_continuous_hasCompactSupport hc hcs)

/-- A measurable essentially bounded function is locally integrable. -/
theorem locallyIntegrable_of_ae_bound {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |f x| ≤ M) :
    LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  (memLp_top_of_bound hf.aestronglyMeasurable (max M 0)
    (by filter_upwards [hM] with x hx; exact (Real.norm_eq_abs _).trans_le (hx.trans
      (le_max_left _ _)))).locallyIntegrable le_top

/-- **Leibniz identity for a `C^∞` weight.** If `g` has weak `ℓ`-derivative `g'` on `V` and
`b` is smooth, then for every test function `φ` supported in `V`,

`∫_V g · (b · ∂_ℓφ) = - ∫_V (g' · b + g · ∂_ℓ b) · φ`.

The product `b · φ` is a smooth compactly supported test function supported inside `V`, so
`HasWeakDerivOn` applies to it directly, and the classical Leibniz rule splits the derivative
of the product. -/
theorem weakDerivOn_smul_test_contDiff {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {b : EuclideanSpace ℝ (Fin d) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x)
      = - ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x := by
  have hbφ_V : tsupport (fun x => b x * φ x) ⊆ V :=
    (closure_mono (Function.support_mul_subset_right b φ)).trans hφV
  have key := hg _ (hb.mul hφc) hφcs.mul_left hbφ_V
  rw [partialD_mul (hb.differentiable (by simp)) (hφc.differentiable (by simp)) ℓ] at key
  have hdb : Continuous (partialD ℓ b) := (contDiff_partialD hb ℓ).continuous
  have hdφ : Continuous (partialD ℓ φ) := (contDiff_partialD hφc ℓ).continuous
  have hdφs : HasCompactSupport (partialD ℓ φ) := hasCompactSupport_partialD hφcs ℓ
  have hint1 : Integrable (fun x => (g x : ℝ) * (b x * partialD ℓ φ x)) (volume.restrict V) :=
    integrable_mul_of_continuous_hasCompactSupport g (hb.continuous.mul hdφ) hdφs.mul_left
  have hint2 : Integrable (fun x => (g x : ℝ) * (partialD ℓ b x * φ x)) (volume.restrict V) :=
    integrable_mul_of_continuous_hasCompactSupport g (hdb.mul hφc.continuous) hφcs.mul_left
  have hintR : Integrable (fun x => (g' x : ℝ) * (b x * φ x)) (volume.restrict V) :=
    integrable_mul_of_continuous_hasCompactSupport g' (hb.continuous.mul hφc.continuous)
      hφcs.mul_left
  have hsplit : ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x + partialD ℓ b x * φ x)
      = (∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hcollect : ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x
      = (∫ x in V, (g' x : ℝ) * (b x * φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hintR hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsplit] at key
  rw [hcollect]
  linarith [key]

/-- A mollification of a locally integrable function against an `L²(V)` class and a continuous
compactly supported function is integrable on `V`. -/
theorem integrable_mul_convolution_normed {V : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (u : Lp ℝ 2 (volume.restrict V))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    Integrable (fun x => (u x : ℝ)
      * ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * ψ x))
      (volume.restrict V) :=
  integrable_mul_of_continuous_hasCompactSupport u
    ((ρ.hasCompactSupport_normed.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf (ρ.contDiff_normed (n := 1)).continuous).mul hψc)
    hψcs.mul_left

/-- **Leibniz identity for a mollified weight.** If `a'` is the weak `ℓ`-derivative of `a`, then
the identity of `weakDerivOn_smul_test_contDiff` holds for the mollification `a ⋆ ρ` with `a'`
mollified in place of `∂_ℓ a`:

`∫_V g · ((a ⋆ ρ) ∂_ℓψ) + ∫_V g · ((a' ⋆ ρ) ψ) = - ∫_V g' · ((a ⋆ ρ) ψ)`. -/
theorem weakDerivOn_mul_convolution_normed {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {a a' : EuclideanSpace ℝ (Fin d) → ℝ}
    (haLI : LocallyIntegrable a (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ha'LI : LocallyIntegrable a' (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ha : HasWeakPartial ℓ a a') (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V) :
    (∫ x in V, (g x : ℝ)
        * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * partialD ℓ ψ x))
      + (∫ x in V, (g x : ℝ)
        * ((a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * ψ x))
    = -(∫ x in V, (g' x : ℝ)
        * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * ψ x)) := by
  have hbcd : ContDiff ℝ (⊤ : ℕ∞) (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI ρ.contDiff_normed
  have hkey := weakDerivOn_smul_test_contDiff ℓ hg hbcd hψc hψcs hψV
  rw [partialD_convolution_eq_of_hasWeakPartial haLI ha ρ.contDiff_normed
    ρ.hasCompactSupport_normed] at hkey
  have hi1 := integrable_mul_convolution_normed haLI ρ g' hψc.continuous hψcs
  have hi2 := integrable_mul_convolution_normed ha'LI ρ g hψc.continuous hψcs
  have hsplit : ∫ x in V, ((g' x : ℝ)
        * (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x
        + (g x : ℝ) * (a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x) * ψ x
      = (∫ x in V, (g' x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * ψ x))
        + ∫ x in V, (g x : ℝ)
          * ((a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ.normed volume)) x * ψ x) := by
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsplit] at hkey
  linarith [hkey]

/-- Convolution with a real kernel is symmetric. -/
theorem convolution_lsmul_comm (F K : EuclideanSpace ℝ (Fin d) → ℝ) :
    F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K = K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F :=
  convolution_symm _ (by ext; simp)

/-- An `L²(V)` class times an essentially bounded measurable function times a continuous
compactly supported one is integrable on `V`. -/
theorem integrable_mul_coeff_mul_continuous {V : Set (EuclideanSpace ℝ (Fin d))}
    (u : Lp ℝ 2 (volume.restrict V)) {c η : EuclideanSpace ℝ (Fin d) → ℝ} (hcm : Measurable c)
    {M : ℝ} (hcM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    (hηc : Continuous η) (hηcs : HasCompactSupport η) :
    Integrable (fun x => (u x : ℝ) * (c x * η x)) (volume.restrict V) := by
  have hc : MemLp c ⊤ (volume.restrict V) := memLp_top_of_bound hcm.aestronglyMeasurable
    (max M 0) (ae_restrict_of_ae (by
      filter_upwards [hcM] with x hx
      exact (Real.norm_eq_abs _).trans_le (hx.trans (le_max_left _ _))))
  exact (Lp.memLp u).integrable_mul
    (MemLp.mul (r := 2) hc (memLp_two_restrict_of_continuous_hasCompactSupport hηc hηcs))

/-- **Mollification limit against an `L²` class.** For a measurable, essentially bounded `c`,
an `L²(V)` class `h` and a continuous compactly supported `η`,

`∫_V h · ((c ⋆ ρₙ) · η) → ∫_V h · (c · η)`

along bumps `ρₙ` with `rOut → 0` and `rOut ≤ 2 rIn`. The mollifications converge to `c` almost
everywhere, are bounded by the essential bound of `c`, and `h · η` is integrable. -/
theorem tendsto_setIntegral_mul_convolution_of_measurable
    {V : Set (EuclideanSpace ℝ (Fin d))}
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hφK : ∀ n, (φ n).rOut ≤ 2 * (φ n).rIn)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} (hcm : Measurable c) {Mc : ℝ}
    (hcM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Mc)
    (h : Lp ℝ 2 (volume.restrict V))
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηc : Continuous η) (hηcs : HasCompactSupport η) :
    Filter.Tendsto
      (fun n => ∫ x in V, (h x : ℝ)
        * ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * η x))
      Filter.atTop (𝓝 (∫ x in V, (h x : ℝ) * (c x * η x))) := by
  have hcLI := locallyIntegrable_of_ae_bound hcm hcM
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) hφ
    (Filter.Eventually.of_forall hφK) hcLI
  have hhη := integrable_mul_of_continuous_hasCompactSupport h hηc hηcs
  refine tendsto_integral_of_dominated_convergence (fun x => max Mc 0 * ‖(h x : ℝ) * η x‖)
    (fun n => (integrable_mul_convolution_normed hcLI (φ n) h hηc hηcs).aestronglyMeasurable)
    (hhη.norm.const_mul _) (fun n => ?_) ?_
  · filter_upwards with x
    have hk := abs_convolution_le_of_measurable ((φ n).nonneg_normed) (φ n).continuous_normed
      (φ n).hasCompactSupport_normed ((φ n).integral_normed) hcm hcM x
    have hk' : ‖(c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x‖
        ≤ max Mc 0 := (Real.norm_eq_abs _).trans_le (hk.trans (le_max_left _ _))
    calc _ = ‖(c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x‖
            * ‖(h x : ℝ) * η x‖ := by simp only [norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk' (norm_nonneg _)
  · filter_upwards [ae_restrict_of_ae hae] with x hx
    simp only [convolution_lsmul_comm c]
    exact (hx.mul_const _).const_mul _

/-- **Weak-derivative Leibniz with a `W^{1,∞}` weight.** If `g` has weak `ℓ`-derivative `g'` on
`V`, and `a` is measurable and essentially bounded with an essentially bounded weak `ℓ`-derivative
`a'`, then `a·g` has weak `ℓ`-derivative `a'·g + a·g'` on `V`.

This is the hypothesis of Guo, *Partial Differential Equations I and II* (Course Lecture
Notes), Theorem VIII.3.2 (p. 65). The identity holds for the mollified weight
(`weakDerivOn_mul_convolution_normed`), and `tendsto_setIntegral_mul_convolution_of_measurable`
sends each of the three terms to its limit. -/
theorem HasWeakDerivOn.mul_isWkInfty_left {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {a a' : EuclideanSpace ℝ (Fin d) → ℝ} (ham : Measurable a) (ha'm : Measurable a')
    (ha : HasWeakPartial ℓ a a') {Ma Mda : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ Ma)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a' x| ≤ Mda)
    (ag : Lp ℝ 2 (volume.restrict V))
    (hag : ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ))
    (dag : Lp ℝ 2 (volume.restrict V))
    (hdag : dag =ᵐ[volume.restrict V] fun x => a' x * (g x : ℝ) + a x * (g' x : ℝ)) :
    HasWeakDerivOn V ℓ ag dag := by
  -- A shrinking family of bumps, with the inner and outer radii in a fixed ratio.
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 2 : ℝ) / 2
      rOut := 1 / (n + 2 : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφrOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  have hφK : ∀ n, (φ n).rOut ≤ 2 * (φ n).rIn := fun n =>
    le_of_eq (by change (1 / (n + 2 : ℝ)) = 2 * (1 / (n + 2 : ℝ) / 2); ring)
  have haLI := locallyIntegrable_of_ae_bound ham haM
  have ha'LI := locallyIntegrable_of_ae_bound ha'm hdaM
  intro ψ hψc hψcs hψV
  have hL1 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ham haM g
    (contDiff_partialD hψc ℓ).continuous (hasCompactSupport_partialD hψcs ℓ)
  have hL2 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ham haM g'
    hψc.continuous hψcs
  have hL3 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ha'm hdaM g
    hψc.continuous hψcs
  have hlim : (∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x))
        + (∫ x in V, (g x : ℝ) * (a' x * ψ x))
      = -(∫ x in V, (g' x : ℝ) * (a x * ψ x)) :=
    tendsto_nhds_unique (hL1.add hL3) (Filter.Tendsto.congr
      (fun n => (weakDerivOn_mul_convolution_normed ℓ hg haLI ha'LI ha (φ n) hψc hψcs hψV).symm)
      hL2.neg)
  have hj1 := integrable_mul_coeff_mul_continuous g ha'm hdaM hψc.continuous hψcs
  have hj2 := integrable_mul_coeff_mul_continuous g' ham haM hψc.continuous hψcs
  have hagInt : ∫ x in V, (ag x : ℝ) * partialD ℓ ψ x
      = ∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x) :=
    integral_congr_ae (by filter_upwards [hag] with x hx; rw [hx]; ring)
  have hdagInt : ∫ x in V, (dag x : ℝ) * ψ x
      = (∫ x in V, (g x : ℝ) * (a' x * ψ x)) + ∫ x in V, (g' x : ℝ) * (a x * ψ x) := by
    rw [← integral_add hj1 hj2]
    exact integral_congr_ae (by filter_upwards [hdag] with x hx; rw [hx]; ring)
  rw [hagInt, hdagInt]
  linarith [hlim]

end EllipticPdes.Regularity
