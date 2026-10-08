/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Embedding.WeakGradUnique

/-!
# Chain rule for weak gradients

A `C¹` function of a class with a weak gradient has a weak gradient, the derivative of the
function at the class times the gradient, once the derivative is bounded. The proof mollifies
the class inside the domain: on the support of a test function, the partials of the
mollifications are the mollified gradient, the classical chain rule and integration by parts
apply to each mollification, and both sides pass to the limit. The function side uses the
Lipschitz bound on `f`; the gradient side uses a subsequence converging almost everywhere and
dominated convergence for the continuous, bounded derivative.

The positive part follows from the chain rule applied to the `C¹` functions
`t ↦ √((t⁺)² + ε²) - ε`, which increase to `t⁺` as `ε` decreases to `0` with derivatives
bounded by one, and from dominated convergence once more. The weak gradient of `u⁺` is the
gradient of `u` where `u > 0` and zero elsewhere. Splitting `u - c` into positive and negative
parts and using uniqueness of the weak gradient, the gradient vanishes almost everywhere on
every level set.

Integrability is asked for locally on the domain throughout, which is the class the sources
state the results for, and the domain is open.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_comp`: the chain rule for a `C¹` function with bounded
  derivative.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart`: the weak gradient of the positive part.
* `EllipticPdes.Embedding.hasWeakGradOn_posPart_sub_const`: the weak gradient of `(u - c)⁺`.
* `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn`: the weak gradient vanishes
  almost everywhere on a level set.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§7.4 Lemma 7.5 (p. 151), Lemma 7.6 and Lemma 7.7 (p. 152);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.10 Problems 17 and 18 (p. 308).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Product of two bounded factors and an integrable one.** -/
theorem integrable_bdd_mul_mul_bdd {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {a b c : α → ℝ} (ha : AEStronglyMeasurable a μ) {A : ℝ} (hA : ∀ x, ‖a x‖ ≤ A)
    (hb : Integrable b μ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ x, ‖c x‖ ≤ C) : Integrable (fun x => a x * b x * c x) μ := by
  refine Integrable.mono' (hb.norm.const_mul (A * C)) ((ha.mul hb.1).mul hc) ?_
  filter_upwards with x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  rw [norm_mul, norm_mul]
  calc ‖a x‖ * ‖b x‖ * ‖c x‖ ≤ A * ‖b x‖ * C := by
        gcongr
        · exact hA x
        · exact hC x
    _ = A * C * ‖b x‖ := by ring

/-- **Lipschitz function of an integrable class against a test factor.** The product with a
continuous compactly supported factor is integrable. -/
theorem integrable_comp_mul_of_lipschitz {w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : Integrable w volume) {f : ℝ → ℝ} {M : ℝ≥0} (hf : LipschitzWith M f)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    Integrable (fun x => f (w x) * h x) volume := by
  have hm : AEStronglyMeasurable (fun x => f (w x) * h x) volume :=
    (hf.continuous.comp_aestronglyMeasurable hw.1).mul hc.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hint1 : Integrable (fun x => ‖h x‖ * ‖w x‖) volume :=
    hw.norm.bdd_mul hc.norm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [norm_norm]; exact hC x)
  have hint2 : Integrable (fun x => ‖h x‖) volume :=
    hc.norm.integrable_of_hasCompactSupport hcs.norm
  refine Integrable.mono' ((hint1.const_mul (M : ℝ)).add (hint2.const_mul |f 0|)) hm ?_
  filter_upwards with x
  have h1 : |f (w x) - f 0| ≤ (M : ℝ) * |w x| := by
    have := hf.dist_le_mul (w x) 0
    simpa [Real.dist_eq] using this
  have h2 : |f (w x)| ≤ (M : ℝ) * |w x| + |f 0| := by
    have : |f (w x)| ≤ |f (w x) - f 0| + |f 0| := by
      have := abs_sub_abs_le_abs_sub (f (w x)) (f 0)
      linarith [abs_nonneg (f 0)]
    linarith
  simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs]
  calc |f (w x)| * |h x| ≤ ((M : ℝ) * |w x| + |f 0|) * |h x| := by gcongr
    _ = (M : ℝ) * (|h x| * |w x|) + |f 0| * |h x| := by ring

/-! ### Elementary closure properties with local integrability -/

/-- **Negation of a weak gradient.** -/
theorem HasWeakGradOn.neg {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B (fun x => -u x) (fun k x => -g k x) := by
  intro φ hφc hφcs hφB k
  have key := h φ hφc hφcs hφB k
  simp only [neg_mul, integral_neg, key, neg_neg]

/-- **Additivity of a weak gradient**, with local integrability on an open set. -/
theorem HasWeakGradOn.add_of_locallyIntegrableOn
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hh : ∀ k, LocallyIntegrableOn (h k) Ω volume)
    (hU : HasWeakGradOn Ω u g) (hV : HasWeakGradOn Ω v h) :
    HasWeakGradOn Ω (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  have hL : ∫ x in Ω, (u x + v x) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) + ∫ x in Ω, v x * partialD k φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      (integrable_mul_of_locallyIntegrableOn hv hφpc hφpcs hps).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hR : ∫ x in Ω, (g k x + h k x) * φ x
      = (∫ x in Ω, g k x * φ x) + ∫ x in Ω, h k x * φ x := by
    rw [← integral_add (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφs).integrableOn
      (integrable_mul_of_locallyIntegrableOn (hh k) hφcont hφcs hφs).integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- **Subtracting a constant** leaves the weak gradient unchanged. -/
theorem hasWeakGradOn_sub_const {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) : HasWeakGradOn Ω (fun x => u x - c) g := by
  intro φ hφc hφcs hφs k
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφs
  -- the integral of a partial of a test function vanishes
  have hzero : ∫ x, partialD k φ x = 0 := by
    have h0 : ∀ x : EuclideanSpace ℝ (Fin d), fderiv ℝ (fun _ => (1 : ℝ)) x = 0 := fun x =>
      by simp
    have hI1 : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))) volume :=
      hφpc.integrable_of_hasCompactSupport hφpcs
    have hI2 : Integrable φ volume := hφc.continuous.integrable_of_hasCompactSupport hφcs
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ => (1 : ℝ)) (g := φ) (v := EuclideanSpace.single k (1 : ℝ))
      (by simp only [h0, _root_.zero_apply, zero_mul]; exact integrable_zero _ _ _)
      (by simpa using hI1) (by simpa using hI2)
      (fun x _ => differentiableAt_const _) (fun x _ => (hφc.differentiable (by simp)) x)
    simp only [one_mul, h0, _root_.zero_apply, zero_mul, integral_zero,
      neg_zero] at key
    simpa [partialD] using key
  have hzeroΩ : ∫ x in Ω, partialD k φ x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hc => hx (hps hc)]
    exact hzero
  have hsplit : ∫ x in Ω, (u x - c) * partialD k φ x
      = (∫ x in Ω, u x * partialD k φ x) - c * ∫ x in Ω, partialD k φ x := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_of_locallyIntegrableOn hu hφpc hφpcs hps).integrableOn
      ((hφpc.integrable_of_hasCompactSupport hφpcs).integrableOn.const_mul c)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hsplit, hzeroΩ, mul_zero, sub_zero, hwg φ hφc hφcs hφs k]

/-! ### Convergence lemmas for the chain rule -/

/-- **The classical chain rule against a test function.** For `f` and `v` of class `C¹` and a
smooth compactly supported `φ`, integration by parts gives
`∫ f(v) ∂ₖφ = -∫ f'(v) ∂ₖv φ`. -/
theorem integral_comp_mul_partialD_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {v φ : EuclideanSpace ℝ (Fin d) → ℝ} (hv : ContDiff ℝ 1 v) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (k : Fin d) :
    ∫ x, f (v x) * partialD k φ x = -∫ x, deriv f (v x) * partialD k v x * φ x := by
  have hfv : ContDiff ℝ 1 (f ∘ v) := hf.comp hv
  have hpc : Continuous (partialD k φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hfderiv : ∀ x, fderiv ℝ (f ∘ v) x (EuclideanSpace.single k (1 : ℝ))
      = deriv f (v x) * partialD k v x := fun x => by
    have h := ((hf.differentiable one_ne_zero) (v x)).hasDerivAt.comp_hasFDerivAt x
      (hv.differentiable one_ne_zero x).hasFDerivAt
    rw [h.fderiv, _root_.smul_apply, smul_eq_mul]
    rfl
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := f ∘ v) (g := φ) (v := EuclideanSpace.single k (1 : ℝ))
    (((hfv.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      hφ.continuous |>.integrable_of_hasCompactSupport hφcs.mul_left)
    ((hfv.continuous.mul hpc).integrable_of_hasCompactSupport hpcs.mul_left)
    ((hfv.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφcs.mul_left)
    (fun x _ => (hfv.differentiable one_ne_zero) x) (fun x _ => (hφ.differentiable (by simp)) x)
  refine key.trans (congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun x => ?_)))
  simp only [hfderiv x]

/-- **The function side of the chain rule.** If `f` is `M`-Lipschitz, `ψ` is bounded and
`vₙ → U` in `L¹`, then `∫ f(vₙ) ψ → ∫ f(U) ψ`. -/
theorem tendsto_integral_comp_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℝ → ℝ} {M : ℝ≥0} (hf : LipschitzWith M f) {ψ : α → ℝ} {C : ℝ} (hψ : ∀ x, ‖ψ x‖ ≤ C)
    {v : ℕ → α → ℝ} {U : α → ℝ} (hv : ∀ n, Integrable (v n) μ) (hU : Integrable U μ)
    (hint : ∀ n, Integrable (fun x => f (v n x) * ψ x) μ)
    (hintU : Integrable (fun x => f (U x) * ψ x) μ)
    (hconv : Tendsto (fun n => eLpNorm (v n - U) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f (v n x) * ψ x ∂μ) atTop (𝓝 (∫ x, f (U x) * ψ x ∂μ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hto : Tendsto (fun n => (M : ℝ) * C * (eLpNorm (v n - U) 1 μ).toReal) atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul
      ((M : ℝ) * C)
  refine squeeze_zero_norm (fun n => ?_) hto
  rw [← integral_sub (hint n) hintU]
  have hbd : Integrable (fun x => (M : ℝ) * C * ‖(v n - U) x‖) μ :=
    ((hv n).sub hU).norm.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Pi.sub_apply, ← sub_mul, norm_mul]
    have h1 : ‖f (v n x) - f (U x)‖ ≤ (M : ℝ) * ‖v n x - U x‖ := by
      simpa [dist_eq_norm] using hf.dist_le_mul (v n x) (U x)
    calc ‖f (v n x) - f (U x)‖ * ‖ψ x‖ ≤ ((M : ℝ) * ‖v n x - U x‖) * C := by gcongr; exact hψ x
      _ = (M : ℝ) * C * ‖v n x - U x‖ := by ring
  · have hm : AEStronglyMeasurable (v n - U) μ := ((hv n).sub hU).aestronglyMeasurable
    rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm hm]

/-- **The gradient side of the chain rule.** If `f'` is continuous and bounded by `M`, `ψ` is
bounded, `vₙ → U` almost everywhere and `wₙ → G` in `L¹`, then
`∫ f'(vₙ) wₙ ψ → ∫ f'(U) G ψ`. -/
theorem tendsto_integral_deriv_comp_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℝ → ℝ} {M : ℝ≥0} (hfc : Continuous (deriv f)) (hM : ∀ t, ‖deriv f t‖ ≤ M)
    {ψ : α → ℝ} {C : ℝ} (hψm : AEStronglyMeasurable ψ μ) (hψ : ∀ x, ‖ψ x‖ ≤ C)
    {v : ℕ → α → ℝ} {U : α → ℝ} (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    {w : ℕ → α → ℝ} {G : α → ℝ} (hw : ∀ n, Integrable (w n) μ) (hG : Integrable G μ)
    (hconv : Tendsto (fun n => eLpNorm (w n - G) 1 μ) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (U x))) :
    Tendsto (fun n => ∫ x, deriv f (v n x) * w n x * ψ x ∂μ) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * ψ x ∂μ)) := by
  have hA : ∀ n, Integrable (fun x => deriv f (v n x) * (w n x - G x) * ψ x) μ := fun n =>
    integrable_bdd_mul_mul_bdd (hfc.comp_aestronglyMeasurable (hvm n)) (fun x => hM _)
      ((hw n).sub hG) hψm hψ
  have hB : ∀ n, Integrable (fun x => deriv f (v n x) * G x * ψ x) μ := fun n =>
    integrable_bdd_mul_mul_bdd (hfc.comp_aestronglyMeasurable (hvm n)) (fun x => hM _) hG hψm hψ
  have hsplit : ∀ n, ∫ x, deriv f (v n x) * w n x * ψ x ∂μ
      = (∫ x, deriv f (v n x) * (w n x - G x) * ψ x ∂μ)
        + ∫ x, deriv f (v n x) * G x * ψ x ∂μ := fun n => by
    rw [← integral_add (hA n) (hB n)]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hpiece1 : Tendsto (fun n => ∫ x, deriv f (v n x) * (w n x - G x) * ψ x ∂μ) atTop (𝓝 0) := by
    have hto : Tendsto (fun n => (M : ℝ) * C * (eLpNorm (w n - G) 1 μ).toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul
        ((M : ℝ) * C)
    refine squeeze_zero_norm (fun n => ?_) hto
    have hbd : Integrable (fun x => (M : ℝ) * C * ‖(w n - G) x‖) μ :=
      ((hw n).sub hG).norm.const_mul _
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans_eq ?_
    · rw [Pi.sub_apply, norm_mul, norm_mul]
      calc ‖deriv f (v n x)‖ * ‖w n x - G x‖ * ‖ψ x‖ ≤ (M : ℝ) * ‖w n x - G x‖ * C := by
            gcongr
            · exact hM _
            · exact hψ x
        _ = (M : ℝ) * C * ‖w n x - G x‖ := by ring
    · have hm : AEStronglyMeasurable (w n - G) μ := ((hw n).sub hG).aestronglyMeasurable
      rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm,
        eLpNorm_one_eq_lintegral_enorm hm]
  have hpiece2 : Tendsto (fun n => ∫ x, deriv f (v n x) * G x * ψ x ∂μ) atTop
      (𝓝 (∫ x, deriv f (U x) * G x * ψ x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (M : ℝ) * C * ‖G x‖)
      (fun n => (hB n).1) (hG.norm.const_mul _) (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul, norm_mul]
      calc ‖deriv f (v n x)‖ * ‖G x‖ * ‖ψ x‖ ≤ (M : ℝ) * ‖G x‖ * C := by
            gcongr
            · exact hM _
            · exact hψ x
        _ = (M : ℝ) * C * ‖G x‖ := by ring
    · filter_upwards [hae] with x hx
      exact (((hfc.tendsto (U x)).comp hx).mul_const (G x)).mul_const (ψ x)
  simpa [hsplit] using hpiece1.add hpiece2

/-- **The chain rule identity for compactly supported integrable extensions.** Let `U` and `G` be
integrable with compact support, `f` of class `C¹` with bounded derivative, `φ` a test function,
and suppose the partial of every standard mollification of `U` agrees with the mollification of
`G` on the support of `φ`. Then `∫ f(U) ∂ₖφ = -∫ f'(U) G φ`. -/
theorem integral_comp_mul_partialD_eq_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0}
    (hM : ∀ t, ‖deriv f t‖₊ ≤ M) {U G φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    (hUint : Integrable U volume) (hUcs : HasCompactSupport U) (hGint : Integrable G volume)
    (hGcs : HasCompactSupport G) (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartial : ∀ n x, partialD k (U ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume) x * φ x
      = (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume) x * φ x) :
    ∫ x, f (U x) * partialD k φ x = -∫ x, deriv f (U x) * G x * φ x := by
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := stdBump δ hδ with hρ
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => U ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ n).normed volume
  set w : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ρ n).normed volume
  have hfl : LipschitzWith M f :=
    lipschitzWith_of_nnnorm_deriv_le (hf.differentiable one_ne_zero) hM
  have hf'c : Continuous (deriv f) := hf.continuous_deriv_one
  have hMr : ∀ t, ‖deriv f t‖ ≤ (M : ℝ) := fun t => by
    have := hM t
    rwa [← NNReal.coe_le_coe, coe_nnnorm] at this
  have hpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφc.continuous
  obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    contDiff_convolution_normed (ρ n) hUint.locallyIntegrable
  have hwint : ∀ n, Integrable (w n) volume := fun n =>
    (contDiff_convolution_normed (ρ n)
      hGint.locallyIntegrable).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_convolution_normed (ρ n) hGcs)
  have hvint : ∀ n, Integrable (v n) volume := fun n =>
    (hvsmooth n).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_convolution_normed (ρ n) hUcs)
  -- `L¹` convergence of the mollifications, and an a.e. convergent subsequence
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (tendsto_eLpNorm_one_stdBump_convolution_sub hδ hUint)).exists_seq_tendsto_ae
  -- the classical identity for every mollification
  have hclassical : ∀ n, ∫ x, f (v n x) * partialD k φ x = -∫ x, deriv f (v n x) * w n x * φ x :=
    fun n => by
      rw [integral_comp_mul_partialD_eq hf ((hvsmooth n).of_le (WithTop.coe_le_coe.mpr le_top))
        hφc hφcs k]
      exact congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun x => by
        dsimp only; rw [mul_assoc, hpartial n x, ← mul_assoc]))
  -- the two limits agree
  have hintU : Integrable (fun x => f (U x) * partialD k φ x) volume :=
    integrable_comp_mul_of_lipschitz hUint hfl hpc hpcs
  have hlimL := (tendsto_integral_comp_mul hfl hCp hvint hUint (fun n =>
    ((hfl.continuous.comp (hvsmooth n).continuous).mul hpc).integrable_of_hasCompactSupport
      hpcs.mul_left) hintU (tendsto_eLpNorm_one_stdBump_convolution_sub hδ hUint)).comp
    hns.tendsto_atTop
  have hlimR := (tendsto_integral_deriv_comp_mul hf'c hMr hφc.continuous.aestronglyMeasurable hCφ
    (fun n => (hvsmooth (ns n)).continuous.aestronglyMeasurable) (fun n => hwint (ns n)) hGint
    ((tendsto_eLpNorm_one_stdBump_convolution_sub hδ hGint).comp hns.tendsto_atTop) hae).neg
  exact tendsto_nhds_unique hlimL (hlimR.congr fun i => (hclassical (ns i)).symm)

/-- **Chain rule for weak gradients** (Gilbarg and Trudinger Lemma 7.5, Evans §5.10 Problem
17). A `C¹` function with bounded derivative, composed with a class with a locally integrable
weak gradient on an open set, has the weak gradient `f'(u) ∇u` there. -/
theorem hasWeakGradOn_comp (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0} (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakGradOn Ω (fun x => f (u x)) (fun k x => deriv f (u x) * g k x) := by
  intro φ hφc hφcs hφΩ k
  -- a compact neighbourhood of the support inside the domain, and the extensions by zero
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hφcs hΩ hφΩ
  set K' := cthickening δ (tsupport φ) with hK'def
  have hK'c : IsCompact K' := IsCompact.cthickening hφcs
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  have huK : IntegrableOn u K' volume := hu.integrableOn_compact_subset hK' hK'c
  have hgK : IntegrableOn (g k) K' volume := (hg k).integrableOn_compact_subset hK' hK'c
  have hcs : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ, HasCompactSupport (K'.indicator h) := fun h =>
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hK'c.isClosed)
  -- on the support of `φ` the partial of the mollification is the mollified gradient
  have hpartial : ∀ n x, partialD k (K'.indicator u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume) x * φ x
      = (K'.indicator (g k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume) x * φ x :=
    fun n x => by
    by_cases hx : x ∈ tsupport φ
    · rw [partialD_convolution_eq_of_hasWeakGradOn hK'm huK (hwg.mono hK') (stdBump δ hδ n) k
        ((closedBall_subset_closedBall (rOut_stdBump_le_self hδ n)).trans
          (closedBall_subset_cthickening hx δ))]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hwhole := integral_comp_mul_partialD_eq_neg hf hM k
    ((integrable_indicator_iff hK'm).mpr huK) (hcs u) ((integrable_indicator_iff hK'm).mpr hgK)
    (hcs (g k)) hφc hφcs hδ hpartial
  -- back to the domain
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφΩ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hps hc), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hφΩ hc), mul_zero]]
  have e1 : (fun x => f (u x) * partialD k φ x)
      = fun x => f (K'.indicator u x) * partialD k φ x := by
    funext x
    by_cases hx : x ∈ K'
    · rw [indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport fun hc =>
        hx (self_subset_cthickening _ (tsupport_partialD_subset k φ hc)), mul_zero, mul_zero]
  have e2 : (fun x => deriv f (u x) * g k x * φ x)
      = fun x => deriv f (K'.indicator u x) * K'.indicator (g k) x * φ x := by
    funext x
    by_cases hx : x ∈ K'
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport fun hc => hx (self_subset_cthickening _ hc), mul_zero,
        mul_zero]
  rw [e1, e2]
  exact hwhole

/-! ### The positive part -/

/-- The `C¹` approximation of the positive part, `√((t⁺)² + ε²) - ε`. -/
private def posPartApprox (ε t : ℝ) : ℝ := Real.sqrt ((max t 0) ^ 2 + ε ^ 2) - ε

/-- The square of the positive part is differentiable, with derivative `2 t⁺`. -/
private theorem hasDerivAt_max_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      (gt_mem_nhds ht).mono fun s hs => by simp [max_eq_right hs.le]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h0
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    simp only [zero_add, max_self, zero_pow two_ne_zero, sub_zero, mul_zero, smul_eq_mul]
    have hcont : Tendsto (fun s : ℝ => max s 0) (𝓝[≠] 0) (𝓝 0) := by
      have hc0 : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
      have := hc0.tendsto (0 : ℝ)
      simp only [max_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hcont.congr' (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun s hs => ?_))
    rcases lt_or_gt_of_ne hs with hs' | hs'
    · simp [max_eq_right hs'.le]
    · simp only [max_eq_left hs'.le]
      field_simp
  · have h0 : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 :=
      (lt_mem_nhds ht).mono fun s hs => by simp [max_eq_left hs.le]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq h0

/-- The square of the positive part is `C¹`. -/
private theorem contDiff_max_sq : ContDiff ℝ 1 fun s : ℝ => (max s 0) ^ 2 := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_max_sq t).differentiableAt, ?_⟩
  rw [funext fun t => (hasDerivAt_max_sq t).deriv]
  exact continuous_const.mul (continuous_id.max continuous_const)

/-- The argument of the square root in `posPartApprox` is positive. -/
private theorem posPartApprox_arg_pos {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) : 0 < (max t 0) ^ 2 + ε ^ 2 := by
  have := pow_pos (abs_pos.mpr hε) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (max t 0)]

/-- The derivative of the approximation. -/
private theorem hasDerivAt_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (posPartApprox ε)
      (2 * max t 0 / (2 * Real.sqrt ((max t 0) ^ 2 + ε ^ 2))) t :=
  (((hasDerivAt_max_sq t).add_const (ε ^ 2)).sqrt (posPartApprox_arg_pos hε t).ne').sub_const ε

/-- The approximation is `C¹`. -/
private theorem contDiff_posPartApprox {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_max_sq.add contDiff_const).sqrt fun t => (posPartApprox_arg_pos hε t).ne').sub
    contDiff_const

/-- The derivative of the approximation, in closed form. -/
private theorem deriv_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    deriv (posPartApprox ε) t = max t 0 / Real.sqrt ((max t 0) ^ 2 + ε ^ 2) := by
  rw [(hasDerivAt_posPartApprox hε t).deriv, mul_div_mul_left _ _ two_ne_zero]

/-- The derivative of the approximation lies in `[0, 1]`. -/
private theorem deriv_posPartApprox_mem {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    0 ≤ deriv (posPartApprox ε) t ∧ deriv (posPartApprox ε) t ≤ 1 := by
  rw [deriv_posPartApprox hε]
  have hm : 0 ≤ max t 0 := le_max_right _ _
  have hs : 0 < Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (posPartApprox_arg_pos hε t)
  refine ⟨div_nonneg hm hs.le, (div_le_one hs).mpr ?_⟩
  exact (Real.le_sqrt hm (posPartApprox_arg_pos hε t).le).mpr (by nlinarith [sq_nonneg ε])

/-- The derivative of the approximation has nonnegative norm at most one. -/
private theorem nnnorm_deriv_posPartApprox_le {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    ‖deriv (posPartApprox ε) t‖₊ ≤ 1 := by
  obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem hε t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h0, NNReal.coe_one]
  exact h1

/-- The approximation lies between `0` and the positive part. -/
private theorem posPartApprox_mem {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ posPartApprox ε t ∧ posPartApprox ε t ≤ max t 0 := by
  have hm : 0 ≤ max t 0 := le_max_right _ _
  unfold posPartApprox
  constructor
  · rw [sub_nonneg]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
      _ ≤ Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (max t 0)])
  · rw [sub_le_iff_le_add]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

/-- The approximation tends to the positive part as `ε → 0`. -/
private theorem tendsto_posPartApprox (t : ℝ) :
    Tendsto (fun ε => posPartApprox ε t) (𝓝 0) (𝓝 (max t 0)) := by
  have hc : Continuous fun ε : ℝ => posPartApprox ε t := by
    unfold posPartApprox
    fun_prop
  have := hc.tendsto 0
  simp only [posPartApprox, zero_pow two_ne_zero, add_zero, sub_zero,
    Real.sqrt_sq (le_max_right t 0)] at this
  exact this

/-- The derivative of the approximation tends to the indicator of `{t > 0}` as `ε → 0`
along positive values. -/
private theorem tendsto_deriv_posPartApprox (t : ℝ) :
    Tendsto (fun n : ℕ => deriv (posPartApprox (1 / (n + 1 : ℝ))) t) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  have hεne : ∀ n : ℕ, (1 / (n + 1 : ℝ)) ≠ 0 := fun n => by positivity
  simp only [fun n => deriv_posPartApprox (hεne n) t]
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hc : Continuous fun ε : ℝ => t / Real.sqrt (t ^ 2 + ε ^ 2) := by
      refine continuous_const.div (continuous_const.add (continuous_id.pow 2)).sqrt fun ε => ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have := (hc.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [Function.comp_def, zero_pow two_ne_zero, add_zero, Real.sqrt_sq ht.le,
      div_self ht.ne'] at this
    exact this
  · rw [max_eq_right (not_lt.mp ht)]
    simp only [zero_div]
    exact tendsto_const_nhds

/-- **Weak gradient of the positive part** (Gilbarg and Trudinger Lemma 7.6, Evans §5.10
Problem 18). On an open set, `u⁺ = max u 0` has the weak gradient `∇u` where `u > 0` and `0`
elsewhere. -/
theorem hasWeakGradOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => max (u x) 0) (fun k x => if 0 < u x then g k x else 0) := by
  intro φ hφc hφcs hφΩ k
  have hφcont : Continuous φ := hφc.continuous
  have hpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hps : tsupport (partialD k φ) ⊆ Ω := (tsupport_partialD_subset k φ).trans hφΩ
  set ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the identity for every approximation
  have hn : ∀ n, ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x
      = -∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x := fun n =>
    hasWeakGradOn_comp hΩ hu hg hwg (contDiff_posPartApprox (hεpos n).ne') (M := 1)
      (nnnorm_deriv_posPartApprox_le (hεpos n).ne') φ hφc hφcs hφΩ k
  -- the function side
  have hL : Tendsto (fun n => ∫ x in Ω, posPartApprox (ε n) (u x) * partialD k φ x) atTop
      (𝓝 (∫ x in Ω, max (u x) 0 * partialD k φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x * partialD k φ x‖)
      (fun n => ((contDiff_posPartApprox (hεpos n).ne').continuous.comp_aestronglyMeasurable
        hum).mul hpc.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn hu hpc hpcs hps).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := posPartApprox_mem (hεpos n).le (u x)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      gcongr
      refine h1.trans ?_
      rw [Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · exact ((tendsto_posPartApprox (u x)).comp hε0).mul_const _
  -- the gradient side
  have hR : Tendsto (fun n => ∫ x in Ω, deriv (posPartApprox (ε n)) (u x) * g k x * φ x) atTop
      (𝓝 (∫ x in Ω, (if 0 < u x then 1 else 0) * g k x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g k x * φ x‖)
      (fun n => (((contDiff_posPartApprox (hεpos n).ne').continuous_deriv_one
        |>.comp_aestronglyMeasurable hum).mul (hg k).aestronglyMeasurable).mul
        hφcont.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn (hg k) hφcont hφcs hφΩ).norm.integrableOn
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem (hεpos n).ne' (u x)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
      calc deriv (posPartApprox (ε n)) (u x) * ‖g k x‖ * ‖φ x‖
          ≤ 1 * ‖g k x‖ * ‖φ x‖ := by gcongr
        _ = ‖g k x‖ * ‖φ x‖ := by ring
    · exact ((tendsto_deriv_posPartApprox (u x)).mul_const _).mul_const _
  have hlim := tendsto_nhds_unique hL (by simp only [hn]; exact hR.neg)
  rw [hlim]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  split_ifs <;> simp

/-- **Weak gradient of `(u - c)⁺`.** -/
theorem hasWeakGradOn_posPart_sub_const (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) (c : ℝ) :
    HasWeakGradOn Ω (fun x => max (u x - c) 0) (fun k x => if c < u x then g k x else 0) := by
  have huc : LocallyIntegrableOn (fun x => u x - c) Ω volume :=
    hu.sub (locallyIntegrableOn_const c)
  have := hasWeakGradOn_posPart hΩ huc hg (hasWeakGradOn_sub_const hu hwg c)
  simpa only [sub_pos] using this

/-- **Local integrability by domination.** -/
theorem locallyIntegrableOn_of_norm_le (hΩ : IsOpen Ω) {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : LocallyIntegrableOn g Ω volume) (hf : AEStronglyMeasurable f (volume.restrict Ω))
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : LocallyIntegrableOn f Ω volume :=
  (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr fun _ hK hKc =>
    (hg.integrableOn_compact_subset hK hKc).norm.mono'
      (hf.mono_measure (Measure.restrict_mono hK le_rfl)) (Eventually.of_forall h)

/-- **Measurability of a truncation.** -/
theorem aestronglyMeasurable_ite_lt {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {u w : EuclideanSpace ℝ (Fin d) → ℝ} (hu : AEStronglyMeasurable u μ)
    (hw : AEStronglyMeasurable w μ) (c : ℝ) :
    AEStronglyMeasurable (fun x => if c < u x then w x else 0) μ := by
  refine ⟨fun x => if c < hu.mk u x then hw.mk w x else 0, ?_, ?_⟩
  · exact StronglyMeasurable.ite
      (measurableSet_lt measurable_const hu.stronglyMeasurable_mk.measurable)
      hw.stronglyMeasurable_mk stronglyMeasurable_const
  · filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x h1 h2
    simp only [h1, h2]

/-- **Local integrability of a truncated gradient.** -/
theorem locallyIntegrableOn_ite_lt (hΩ : IsOpen Ω) {u w : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict Ω)) (hw : LocallyIntegrableOn w Ω volume)
    (c : ℝ) : LocallyIntegrableOn (fun x => if c < u x then w x else 0) Ω volume :=
  locallyIntegrableOn_of_norm_le hΩ hw (aestronglyMeasurable_ite_lt hu hw.aestronglyMeasurable c)
    fun x => by split_ifs <;> simp

/-- **Local integrability of the positive part of `u - c`.** -/
theorem locallyIntegrableOn_posPart_sub_const (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume) (c : ℝ) :
    LocallyIntegrableOn (fun x => max (u x - c) 0) Ω volume := by
  refine locallyIntegrableOn_of_norm_le hΩ (hu.sub (locallyIntegrableOn_const c))
    (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hu.aestronglyMeasurable) fun x => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Vanishing of the weak gradient on level sets** (Gilbarg and Trudinger Lemma 7.7). On an
open set, the weak gradient of `u` is zero almost everywhere on `{u = c}`. -/
theorem ae_eq_zero_of_eq_const_of_hasWeakGradOn (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) (c : ℝ) (k : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), u x = c → g k x = 0 := by
  have hum : AEStronglyMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable
  -- the positive parts of `u - c` and of `-u - (-c)`
  have hpos := hasWeakGradOn_posPart_sub_const hΩ hu hg hwg c
  have hneg := hasWeakGradOn_posPart_sub_const hΩ hu.neg (fun j => (hg j).neg) hwg.neg (-c)
  have hind : ∀ j, LocallyIntegrableOn (fun x => if c < u x then g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum (hg j) c
  have hind' : ∀ j, LocallyIntegrableOn (fun x => if -c < -u x then -g j x else 0) Ω volume :=
    fun j => locallyIntegrableOn_ite_lt hΩ hum.neg (hg j).neg (-c)
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart_sub_const hΩ hu c)
    (locallyIntegrableOn_posPart_sub_const hΩ hu.neg (-c)).neg hind (fun j => (hind' j).neg)
    hneg.neg
  -- the sum is `u - c`, whose weak gradient is `g`
  have heq : (fun x => max (u x - c) 0 + -max (-u x - -c) 0) = fun x => u x - c := by
    funext x
    rw [neg_sub_neg, ← neg_sub (u x) c, ← sub_eq_add_neg, max_zero_sub_max_neg_zero_eq_self]
  simp only [Pi.neg_apply] at hsum
  rw [heq] at hsum
  have hsumint : ∀ j, LocallyIntegrableOn
      (fun x => (if c < u x then g j x else 0) + -(if -c < -u x then -g j x else 0)) Ω volume :=
    fun j => (hind j).add (hind' j).neg
  have huniq := hasWeakGradOn_unique_ae_of_locallyIntegrableOn hΩ hg hsumint
    (hasWeakGradOn_sub_const hu hwg c) hsum k
  filter_upwards [huniq] with x hx hxc
  rw [hx]
  simp [hxc]

/-- **Weak gradient of the negative part** (Gilbarg and Trudinger Lemma 7.6, second clause).
`u⁻ = min u 0` has the weak gradient `∇u` where `u < 0` and `0` elsewhere. -/
theorem hasWeakGradOn_negPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => min (u x) 0) (fun k x => if u x < 0 then g k x else 0) := by
  have h := (hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg).neg
  refine h.congr_ae (Eventually.of_forall fun x => ?_) fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    by_cases hx : u x ≤ 0
    · rw [min_eq_left hx, max_eq_left (by linarith), neg_neg]
    · have hx' : 0 < u x := not_le.mp hx
      rw [min_eq_right hx'.le, max_eq_right (by linarith), neg_zero]
  · simp only [Pi.neg_apply, neg_pos]
    split_ifs <;> simp

/-- Local integrability of the positive part. -/
theorem locallyIntegrableOn_posPart (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) :
    LocallyIntegrableOn (fun x => max (u x) 0) Ω volume := by
  have := locallyIntegrableOn_posPart_sub_const hΩ hu 0
  simpa only [sub_zero] using this

/-- **Weak gradient of the absolute value** (Gilbarg and Trudinger Lemma 7.6, third clause).
`|u|` has the weak gradient `∇u` where `u > 0`, `-∇u` where `u < 0`, and `0` elsewhere. -/
theorem hasWeakGradOn_abs (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume) (hwg : HasWeakGradOn Ω u g) :
    HasWeakGradOn Ω (fun x => |u x|)
      fun k x => if 0 < u x then g k x else if u x < 0 then -g k x else 0 := by
  have hpos := hasWeakGradOn_posPart hΩ hu hg hwg
  have hneg := hasWeakGradOn_posPart hΩ hu.neg (fun k => (hg k).neg) hwg.neg
  have hsum := hpos.add_of_locallyIntegrableOn (locallyIntegrableOn_posPart hΩ hu)
    (locallyIntegrableOn_posPart hΩ hu.neg)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.aestronglyMeasurable (hg k) 0)
    (fun k => locallyIntegrableOn_ite_lt hΩ hu.neg.aestronglyMeasurable (hg k).neg 0) hneg
  refine hsum.congr_ae (Eventually.of_forall fun x => ?_)
    fun k => Eventually.of_forall fun x => ?_
  · simp only [Pi.neg_apply]
    exact max_zero_add_max_neg_zero_eq_abs_self (u x)
  · simp only [Pi.neg_apply, neg_pos]
    rcases lt_trichotomy (u x) 0 with h | h | h
    · have h' : ¬ 0 < u x := not_lt.mpr h.le
      simp [h, h']
    · simp [h]
    · have h' : ¬ u x < 0 := not_lt.mpr h.le
      simp [h, h']

end EllipticPdes.Embedding
