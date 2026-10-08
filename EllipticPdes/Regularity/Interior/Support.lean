/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.RestrictedDiffQuotientMem
public import EllipticPdes.Regularity.CoeffC1
public import EllipticPdes.Regularity.CutoffTower

/-!
# Internal support lemmas for the interior estimate

Shared scaffolding for the modules under `EllipticPdes.Regularity.Interior`. These declarations
are internal: they are exposed only because Lean's `private` modifier is file-scoped and
the interior estimate spans several modules. Each lemma here is stated and proved once but
consumed in more than one of them, so no single module can keep it private.

Consumers should use `interior_H2_estimate` and its siblings from
`EllipticPdes.Regularity.Interior`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A cutoff-multiplied class vanishes a.e. off the topological support of the cutoff. -/
lemma mulTest_ae_eq_zero_off_tsupport {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) (g : L2D Ω) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ tsupport η → (mulTest hη g x : ℝ) = 0 := by
  filter_upwards [mulCutoff_coeFn hη g] with x hx hxns
  rw [hx, image_eq_zero_of_notMem_tsupport hxns, zero_mul]

/-- If a class `g` vanishes a.e. (on `Ω`) off a set `S`, then its extension by zero to the
whole space is a.e. supported in `S`. -/
lemma extendL2_supp_of_ae_restrict (hΩm : MeasurableSet Ω) (g : L2D Ω)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hg : ∀ᵐ x ∂(volume.restrict Ω), x ∉ S → (g x : ℝ) = 0) :
    ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S := by
  filter_upwards [coeFn_extendL2 hΩm g, ae_imp_of_ae_restrict hg] with x hx himp
  rw [hx]; intro hne
  by_cases hxΩ : x ∈ Ω
  · by_contra hxS
    rw [Set.indicator_of_mem hxΩ] at hne
    exact hne (himp hxΩ hxS)
  · rw [Set.indicator_of_notMem hxΩ] at hne; exact absurd rfl hne

/-- If a class `g` agrees a.e. on `Ω` with a function `F` that vanishes off `Ω`, then its
extension by zero agrees a.e. with `F` on the whole space. -/
lemma coeFn_extendL2_of_ae_restrict (hΩm : MeasurableSet Ω) (g : L2D Ω)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hg : g =ᵐ[volume.restrict Ω] F)
    (hF : ∀ x, x ∉ Ω → F x = 0) :
    (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] F := by
  filter_upwards [coeFn_extendL2 hΩm g, ae_imp_of_ae_restrict hg] with x hx himp
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ]; exact himp hxΩ
  · rw [Set.indicator_of_notMem hxΩ, hF x hxΩ]

/-- The inner product of two `L²` classes is the integral of the product of any representatives. -/
lemma inner_Lp_eq_integral_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : Lp ℝ 2 μ} {F G : α → ℝ} (hf : f =ᵐ[μ] F) (hg : g =ᵐ[μ] G) :
    ⟪f, g⟫ = ∫ x, F x * G x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [Real.inner_apply, h1, h2]

/-- **Invisibility of a cutoff on the set where it is `1`.** If `η ≡ 1` on `V ⊆ Ω`, the
`V`-restriction of the whole-space extension of `η · g` agrees with that of `g`. -/
theorem restrictL2_extendL2_mulTest_of_eqOn (hΩm : MeasurableSet Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω)
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (h1 : Set.EqOn η 1 V) (g : L2D Ω) :
    restrictL2 (Ω := V) (extendL2 hΩm (mulTest hη g)) = restrictL2 (Ω := V) (extendL2 hΩm g) := by
  have hmt : (mulTest hη g : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict V] fun x => η x * (g x : ℝ) :=
    (mulCutoff_coeFn hη g).filter_mono (ae_mono (Measure.restrict_mono hVΩ le_rfl))
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm (mulTest hη g)),
    coeFn_restrictL2 (Ω := V) (extendL2 hΩm g),
    ae_restrict_of_ae (coeFn_extendL2 hΩm (mulTest hη g)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g), hmt, ae_restrict_mem hVm]
    with x h1' h2' h3 h4 hmtx hxV
  rw [h1', h2', h3, h4, Set.indicator_of_mem (hVΩ hxV), Set.indicator_of_mem (hVΩ hxV), hmtx,
    h1 hxV, Pi.one_apply, one_mul]

/-- An integral over `Ω` of an integrand vanishing off `W ⊆ Ω` is an integral over `W`. -/
theorem setIntegral_shrink_of_forall_eq_zero
    {W Ω : Set (EuclideanSpace ℝ (Fin d))} (hWΩ : W ⊆ Ω)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ∀ x, x ∉ W → F x = 0) :
    ∫ x in Ω, F x = ∫ x in W, F x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hF x (fun hc => hx (hWΩ hc))),
    setIntegral_eq_integral_of_forall_compl_eq_zero hF]

/-- The restriction to `V ⊆ Ω` of the whole-space extension of an `L²(Ω)` class agrees with the
class itself on `V`. -/
theorem coeFn_restrictL2_extendL2_of_subset {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) (g : L2D Ω) :
    (restrictL2 (Ω := V) (extendL2 hΩm g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict V] (g : EuclideanSpace ℝ (Fin d) → ℝ) := by
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm g),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hVm] with x h1 h2 h3
  rw [h1, h2, Set.indicator_of_mem (hVΩ h3)]

/-- An integral over `Ω` of a weight times an `L²(Ω)` class times a function vanishing off
`V ⊆ Ω` is the integral over `V` against the restricted extension of the class. -/
theorem setIntegral_mul_restrictL2_extendL2 {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) (g : L2D Ω)
    (c w : EuclideanSpace ℝ (Fin d) → ℝ) (hw : ∀ x, x ∉ V → w x = 0) :
    ∫ x in Ω, c x * (g x : ℝ) * w x
      = ∫ x in V, c x * (restrictL2 (Ω := V) (extendL2 hΩm g) x : ℝ) * w x := by
  rw [setIntegral_shrink_of_forall_eq_zero hVΩ (fun x hx => by rw [hw x hx, mul_zero])]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictL2_extendL2_of_subset hΩm hVm hVΩ g] with x hx
  rw [hx]

/-- Restriction to `Ω` is non-expansive on `L²`: `‖restrictL2 w‖ ≤ ‖w‖`. -/
lemma norm_restrictL2_le (w : EucL2 d) :
    ‖restrictL2 (Ω := Ω) w‖ ≤ ‖w‖ :=
  norm_Lp_toLp_restrict_le Ω w

/-- Abstract single-term ≤ sum over `Fin d` for a nonnegative real family, isolated so its
application only beta-reduces (avoiding a `Finset.single_le_sum` isDefEq loop on `L²` norm
summands). -/
lemma single_le_sum_fin {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) (k : Fin m) :
    g k ≤ ∑ i : Fin m, g i :=
  Finset.single_le_sum (f := g) (fun i _ => hg i) (Finset.mem_univ k)

end EllipticPdes.Regularity
