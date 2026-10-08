/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Extension.Basic

/-!
# Cutting a pair off inside a neighbourhood

Guo's Theorem III.2.2 finishes by covering the boundary with finitely many chart
neighbourhoods and gluing the local extensions with a partition of unity. Each piece of that
partition is a cutoff supported in one chart's ball, and the piece it cuts out has to reach the
whole region above that chart's graph, where the chart describes the domain only inside the
ball.

A cutoff `η` supported in `W` sends a class `u` with weak gradient `g` on `B ∩ W` to the class
`η u` with weak gradient `η gₖ + ∂ₖη u` on all of `B`. This is the linear map `cutOp η` on
pairs, and the file bounds it in every `Lᵖ` seminorm.

## Main declarations

* `EllipticPdes.Extension.cutOp`: multiplication of a pair by a cutoff, as a linear map.
* `EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter`: the weak gradient of a class cut off
  inside a neighbourhood, on the surrounding set.
* `EllipticPdes.Extension.cutOp_spec`: the weak gradient and the integrability of the pair
  `cutOp η (u, g)`.
* `EllipticPdes.Extension.eLpNorm_cutoff_mul_le` and
  `EllipticPdes.Extension.eLpNorm_cutOp_snd_le`: its bound in every `Lᵖ` seminorm.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn partialD_mul)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability from a neighbourhood the class vanishes outside.** A class integrable on the
part of a set inside `W` and vanishing off `W` is integrable on the whole set, the rest of it
contributing nothing. -/
theorem integrableOn_of_vanishing_off {B W : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) (hW : MeasurableSet W) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : IntegrableOn f (B ∩ W) volume) (hoff : ∀ x, x ∉ W → f x = 0) :
    IntegrableOn f B volume := by
  have hdiff : IntegrableOn f (B \ W) volume := by
    refine (integrableOn_zero (μ := volume) (s := B \ W)).congr_fun ?_ (hB.diff hW)
    intro x hx
    exact (hoff x hx.2).symm
  exact Set.inter_union_sdiff B W ▸ hf.union hdiff

/-- An integral over `B` of a function vanishing off `W` is the integral over `B ∩ W`. -/
theorem setIntegral_eq_inter {B W : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hoff : ∀ x, x ∉ W → F x = 0) :
    ∫ x in B, F x = ∫ x in B ∩ W, F x :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB Set.inter_subset_left fun x hx =>
    hoff x fun hc => hx.2 ⟨hx.1, hc⟩

/-- A smooth function vanishes, with its partial derivatives, off a set containing its support. -/
theorem partialD_eq_zero_of_notMem {W : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηs : tsupport η ⊆ W) (k : Fin d)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ W) : partialD k η x = 0 := by
  have hxs : x ∉ tsupport η := fun hc => hx (hηs hc)
  have hev : η =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hxs] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [partialD, hev.fderiv_eq]
  simp

/-- **Weak gradient of a class cut off inside a neighbourhood.** If `u` has weak gradient `g` on
`B ∩ W` and `η` is smooth with `tsupport η ⊆ W`, then `η u` has weak gradient
`η gₖ + u ∂ₖη` on all of `B`. Testing against `φ` reduces to testing the hypothesis against
`η φ`, whose support sits inside `B ∩ W`, and both sides of the identity see only `W`, the
cutoff and its derivative vanishing off it. -/
theorem hasWeakGradOn_mul_cutoff_inter {B W : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ W)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (B ∩ W) volume) (hgi : ∀ k, IntegrableOn (g k) (B ∩ W) volume)
    (h : HasWeakGradOn (B ∩ W) u g) :
    HasWeakGradOn B (fun x => η x * u x)
      (fun k x => η x * g k x + partialD k η x * u x) := by
  intro φ hφc hφcs hφs k
  have hηd : Differentiable ℝ η := hηc.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  have hηpc : Continuous (partialD k η) := hηc.continuous_partialD (by simp) k
  have hφpc : Continuous (partialD k φ) := hφc.continuous_partialD (by simp) k
  -- the test function, pushed inside the neighbourhood
  have hψs : tsupport (fun x => η x * φ x) ⊆ B ∩ W :=
    fun x hx => ⟨hφs ((closure_mono (Function.support_mul_subset_right η φ)) hx),
      hηs ((closure_mono (Function.support_mul_subset_left η φ)) hx)⟩
  have key := h _ (hηc.mul hφc) hφcs.mul_left hψs k
  have hi1 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) (B ∩ W) volume :=
    hu.mul_of_hasCompactSupport (hηc.continuous.mul hφpc) (hφcs.partialD k).mul_left
  have hi2 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) (B ∩ W) volume :=
    hu.mul_of_hasCompactSupport (hηpc.mul hφc.continuous) hφcs.mul_left
  have hi3 : IntegrableOn (fun x => g k x * (η x * φ x)) (B ∩ W) volume :=
    (hgi k).mul_of_hasCompactSupport (hηc.continuous.mul hφc.continuous) hφcs.mul_left
  -- the product rule inside the test function, and the split it licenses
  have hsplit : ∫ x in B ∩ W, u x * partialD k (fun y => η y * φ y) x
      = (∫ x in B ∩ W, u x * (partialD k η x * φ x))
        + ∫ x in B ∩ W, u x * (η x * partialD k φ x) := by
    rw [← integral_add hi2 hi1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [partialD_mul k (hηd x) (hφd x)]; ring)
  rw [hsplit] at key
  -- both sides of the goal see only the neighbourhood
  rw [setIntegral_eq_inter hB (W := W) (F := fun x => η x * u x * partialD k φ x) fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport fun hc => hx (hηs hc)],
    setIntegral_eq_inter hB (W := W)
      (F := fun x => (η x * g k x + partialD k η x * u x) * φ x) fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport fun hc => hx (hηs hc),
        partialD_eq_zero_of_notMem hηs k hx]]
  have hgoalR : ∫ x in B ∩ W, (η x * g k x + partialD k η x * u x) * φ x
      = (∫ x in B ∩ W, g k x * (η x * φ x))
        + ∫ x in B ∩ W, u x * (partialD k η x * φ x) := by
    rw [← integral_add hi3 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hgoalR]
  have hgoalL : ∫ x in B ∩ W, η x * u x * partialD k φ x
      = ∫ x in B ∩ W, u x * (η x * partialD k φ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hgoalL]
  linarith [key]

/-- **Multiplication of a pair by a cutoff**, as a linear map. The second component is the
product rule. -/
def cutOp (η : EuclideanSpace ℝ (Fin d) → ℝ) : SobolevPair d →ₗ[ℝ] SobolevPair d where
  toFun w := (fun x => η x * w.1 x, fun k x => η x * w.2 k x + partialD k η x * w.1 x)
  map_add' w w' := by
    refine Prod.ext (funext fun x => ?_) (funext fun k => funext fun x => ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply] <;> ring
  map_smul' a w := by
    refine Prod.ext (funext fun x => ?_) (funext fun k => funext fun x => ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      ring

/-- The first component of `cutOp η w`. -/
@[simp] theorem cutOp_fst (η : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    (cutOp η w).1 = fun x => η x * w.1 x := rfl

/-- The second component of `cutOp η w`, the product rule. -/
@[simp] theorem cutOp_snd (η : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    (cutOp η w).2 = fun k x => η x * w.2 k x + partialD k η x * w.1 x := rfl

/-- **Integrability of the cut-off pair.** If `u` and `g` are integrable on `B ∩ W` and `η` is
smooth with compact support inside `W`, both components of `cutOp η (u, g)` are integrable
on `B`. -/
theorem integrableOn_cutOp {B W : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    (hW : MeasurableSet W) {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηc : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcs : HasCompactSupport η) (hηs : tsupport η ⊆ W)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (B ∩ W) volume) (hgi : ∀ k, IntegrableOn (g k) (B ∩ W) volume) :
    IntegrableOn (cutOp η (u, g)).1 B volume ∧
      ∀ k, IntegrableOn ((cutOp η (u, g)).2 k) B volume := by
  have hoff : ∀ x, x ∉ W → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hηs hc)
  refine ⟨integrableOn_of_vanishing_off hB hW (hu.hasCompactSupport_mul hηc.continuous hηcs)
      fun x hx => by simp [hoff x hx], fun k => ?_⟩
  exact integrableOn_of_vanishing_off hB hW
    (((hgi k).hasCompactSupport_mul hηc.continuous hηcs).add
      (hu.hasCompactSupport_mul (hηc.continuous_partialD (by simp) k) (hηcs.partialD k)))
    fun x hx => by simp [hoff x hx, partialD_eq_zero_of_notMem hηs k hx]

/-- **The cut-off pair.** If `(u, g)` has a weak gradient on `B ∩ W` and `η` is smooth with
compact support inside `W`, then `cutOp η (u, g)` has a weak gradient on `B`, and both of its
components are integrable there. -/
theorem cutOp_spec {B W : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    (hW : MeasurableSet W) {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηc : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcs : HasCompactSupport η) (hηs : tsupport η ⊆ W)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (B ∩ W) volume) (hgi : ∀ k, IntegrableOn (g k) (B ∩ W) volume)
    (h : HasWeakGradOn (B ∩ W) u g) :
    HasWeakGradOn B (cutOp η (u, g)).1 (cutOp η (u, g)).2 ∧
      IntegrableOn (cutOp η (u, g)).1 B volume ∧
      ∀ k, IntegrableOn ((cutOp η (u, g)).2 k) B volume :=
  ⟨hasWeakGradOn_mul_cutoff_inter hB hηc hηs hu hgi h,
    integrableOn_cutOp hB hW hηc hηcs hηs hu hgi⟩

/-- **Seminorm of a class cut off inside a neighbourhood.** The cutoff vanishes off `W`, and on
`S ∩ W` the class is read on `T`, so the product over `S` is bounded by the supremum of the
cutoff against the seminorm over `T`. This is what lets an estimate taken over the region above
a chart's graph be stated against the domain. -/
theorem eLpNorm_cutoff_mul_le {S W T : Set (EuclideanSpace ℝ (Fin d))}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    {η v : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hC : ∀ y, ‖η y‖ ≤ C)
    (hηm : AEStronglyMeasurable η (volume.restrict S))
    (hv : AEStronglyMeasurable v (volume.restrict T))
    (hoff : ∀ y, y ∉ W → η y = 0) (hSW : S ∩ W ⊆ T) {p : ℝ≥0∞} :
    eLpNorm (fun y => η y * v y) p (volume.restrict S)
      ≤ ENNReal.ofReal C * eLpNorm v p (volume.restrict T) := by
  have hvT : AEStronglyMeasurable (T.indicator v) volume :=
    (aestronglyMeasurable_indicator_iff hT).2 hv
  have hptwise : ∀ y ∈ S, η y * v y = η y * T.indicator v y := fun y hy => by
    by_cases hyW : y ∈ W
    · rw [Set.indicator_of_mem (hSW ⟨hy, hyW⟩)]
    · rw [hoff y hyW, zero_mul, zero_mul]
  have heq : (fun y => η y * v y) =ᵐ[volume.restrict S] fun y => η y * T.indicator v y :=
    (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hptwise)
  calc eLpNorm (fun y => η y * v y) p (volume.restrict S)
      = eLpNorm (fun y => T.indicator v y * η y) p (volume.restrict S) :=
        eLpNorm_congr_ae (heq.trans (Filter.Eventually.of_forall fun y => mul_comm _ _))
    _ ≤ ENNReal.ofReal C * eLpNorm (T.indicator v) p (volume.restrict S) :=
        eLpNorm_mul_le_of_bound ((hvT.mono_measure Measure.restrict_le_self).mul hηm) hC
    _ ≤ ENNReal.ofReal C * eLpNorm (T.indicator v) p volume :=
        mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _
    _ = ENNReal.ofReal C * eLpNorm v p (volume.restrict T) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet]

/-- **Bound on the second component of a cut-off pair.** -/
theorem eLpNorm_cutOp_snd_le {S W T : Set (EuclideanSpace ℝ (Fin d))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ W) {C : ℝ} (hC : ∀ y, ‖η y‖ ≤ C)
    (k : Fin d) (hCd : ∀ y, ‖partialD k η y‖ ≤ C) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u g : EuclideanSpace ℝ (Fin d) → ℝ} (hu : AEStronglyMeasurable u (volume.restrict T))
    (hg : AEStronglyMeasurable g (volume.restrict T)) (hSW : S ∩ W ⊆ T) :
    eLpNorm (fun y => η y * g y + partialD k η y * u y) p (volume.restrict S)
      ≤ ENNReal.ofReal C * (eLpNorm g p (volume.restrict T) + eLpNorm u p (volume.restrict T)) := by
  have hoff : ∀ y, y ∉ W → η y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hc => hy (hηs hc)
  have hoffd : ∀ y, y ∉ W → partialD k η y = 0 := fun y hy => partialD_eq_zero_of_notMem hηs k hy
  have hηm : AEStronglyMeasurable η (volume.restrict S) := hηc.continuous.aestronglyMeasurable
  have hdm : AEStronglyMeasurable (partialD k η) (volume.restrict S) :=
    (hηc.continuous_partialD (by simp) k).aestronglyMeasurable
  exact (eLpNorm_add_le hp).trans
    ((add_le_add (eLpNorm_cutoff_mul_le hS hT hC hηm hg hoff hSW)
      (eLpNorm_cutoff_mul_le hS hT hCd hdm hu hoffd hSW)).trans_eq (by rw [mul_add]))

/-- **A pair cut off inside a measurable set, on the whole space.** If `(U, G)` has a weak
gradient on `W`, with integrable components there, and `η` is smooth with compact support inside
`W` and bounded together with its partials by `C`, then `cutOp η (U, G)` has a weak gradient on
the whole space, integrable components, and seminorms bounded by `C` times those of `(U, G)`
over `W`. -/
theorem cutOp_global {W : Set (EuclideanSpace ℝ (Fin d))} (hW : MeasurableSet W)
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η)
    (hηs : tsupport η ⊆ W) {C : ℝ} (hC : ∀ y, ‖η y‖ ≤ C)
    (hCd : ∀ (k : Fin d) y, ‖partialD k η y‖ ≤ C) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {U : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IntegrableOn U W volume) (hG : ∀ k, IntegrableOn (G k) W volume)
    (hwg : HasWeakGradOn W U G) {N K₁ K₂ : ℝ≥0∞}
    (h₁ : eLpNorm U p (volume.restrict W) ≤ K₁ * N)
    (h₂ : ∀ k, eLpNorm U p (volume.restrict W) + eLpNorm (G k) p (volume.restrict W) ≤ K₂ * N) :
    HasWeakGradOn Set.univ (cutOp η (U, G)).1 (cutOp η (U, G)).2 ∧
      Integrable (cutOp η (U, G)).1 volume ∧ (∀ k, Integrable ((cutOp η (U, G)).2 k) volume) ∧
      eLpNorm (cutOp η (U, G)).1 p volume ≤ ENNReal.ofReal C * (K₁ * N) ∧
      ∀ k, eLpNorm ((cutOp η (U, G)).2 k) p volume ≤ ENNReal.ofReal C * (K₂ * N) := by
  have hUW : IntegrableOn U (Set.univ ∩ W) volume := by simpa using hU
  have hGW : ∀ k, IntegrableOn (G k) (Set.univ ∩ W) volume := fun k => by simpa using hG k
  obtain ⟨hw, hi, hgi⟩ := cutOp_spec MeasurableSet.univ hW hηc hηcs hηs hUW hGW
    (by simpa using hwg)
  have hsub : Set.univ ∩ W ⊆ W := Set.inter_subset_right
  refine ⟨hw, integrableOn_univ.1 hi, fun k => integrableOn_univ.1 (hgi k), ?_, fun k => ?_⟩
  · have := eLpNorm_cutoff_mul_le MeasurableSet.univ hW hC hηc.continuous.aestronglyMeasurable
      hU.1 (fun y hy => image_eq_zero_of_notMem_tsupport fun hc => hy (hηs hc)) hsub (p := p)
    rw [Measure.restrict_univ] at this
    exact this.trans (mul_le_mul_right h₁ _)
  · have := eLpNorm_cutOp_snd_le MeasurableSet.univ hW hηc hηs hC k (hCd k) hp hU.1 (hG k).1 hsub
    rw [Measure.restrict_univ] at this
    exact this.trans (mul_le_mul_right (by rw [add_comm]; exact h₂ k) _)

end EllipticPdes.Extension
