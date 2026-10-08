/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.DifferentiatedEquation
public import EllipticPdes.Regularity.WeakFormDense

/-!
# Localising the bilinear pairing to plain integrals

The weak formulation a solution satisfies pairs `H1amb Ω` vectors through the bounded bilinear
form `Op.fullBilin`. Every localised step of interior regularity instead works with plain
integrals over a compact `V ⊆ Ω` against a test function supported in `V`, on
`Lp ℝ 2 (volume.restrict V)` classes. This file is the bridge between the two.

A test function supported in `V` has its graph in `H₀¹(Ω)`, so the weak formulation applies to
it. `fullBilin_testGraph_eq` expands the pairing into integrals over `Ω`, each integrand has a
factor vanishing off `tsupport v ⊆ V`, so the integral shrinks to `V`, and the restriction of
the whole-space extension of each coordinate agrees with that coordinate on `V`.

The localised identity is the hypothesis `hLoc` of `differentiated_weakForm_of_pairs`, so the
differentiated-equation identity of Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2, follows from the weak formulation itself.

## Main declarations

* `localWeakForm_of_fullBilin`: the localised plain-integral weak identity on `V`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Localised plain-integral weak identity -/

/-- **Localised weak formulation (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2).** A weak solution `u ∈ H₀¹(Ω)` of `L u = f`, stated through the bilinear pairing
`Op.fullBilin` over all of `Ω`, satisfies the plain-integral identity `∑_{i,j} ∫_V a_{ij}(∂ᵢu)
∂ⱼv + ∑_i ∫_V b_i (∂ᵢu) v + ∫_V c u v = ∫_V f v` on any measurable `V ⊆ Ω`, for every test
function `v` with `tsupport v ⊆ V`, with each coordinate read as the `V`-restriction of its
whole-space extension by zero. This is the shape the differentiated-equation identity takes as
its hypothesis `hLoc`. -/
theorem localWeakForm_of_fullBilin (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) (hvc : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvcs : HasCompactSupport v) (hvV : tsupport v ⊆ V) :
    (∑ i : Fin d, ∑ j : Fin d, ∫ x in V, Op.a x i j
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * partialD j v x)
      + (∑ i : Fin d, ∫ x in V, Op.b x i
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * v x)
      + (∫ x in V, Op.c x
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ) * v x)
      = ∫ x in V, (restrictL2 (Ω := V) (extendL2 hΩm f) x : ℝ) * v x := by
  classical
  have hv : IsTestFn Ω v := ⟨hvc, hvcs, hvV.trans hVΩ⟩
  have hv0 : ∀ x, x ∉ V → v x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hvV hc))
  have hdv0 : ∀ j x, x ∉ V → partialD j v x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hvV (tsupport_partialD_subset j v hc)))
  have hkey := hu ⟨hv.testGraph, testGraph_mem_H01 hv⟩
  rw [fullBilin_testGraph_eq Op u hv] at hkey
  have hfun : (⟨hv.testGraph, testGraph_mem_H01 hv⟩ : H01 Ω).1 0 =ᵐ[volume.restrict Ω] v := by
    rw [show (⟨hv.testGraph, testGraph_mem_H01 hv⟩ : H01 Ω).1 0 = hv.mem_lp.toLp v from
      IsTestFn.testGraph_zero hv]
    exact hv.mem_lp.coeFn_toLp
  have hdat : (∫ x in Ω, (f x : ℝ)
      * ((⟨hv.testGraph, testGraph_mem_H01 hv⟩ : H01 Ω).1 0 x : ℝ))
      = ∫ x in V, (restrictL2 (Ω := V) (extendL2 hΩm f) x : ℝ) * v x := by
    rw [integral_congr_ae (by filter_upwards [hfun] with x hx; rw [hx])]
    simpa using setIntegral_mul_restrictL2_extendL2 hΩm hVm hVΩ f (fun _ => 1) v hv0
  rw [hdat] at hkey
  rw [← hkey]
  simp only [← setIntegral_mul_restrictL2_extendL2 hΩm hVm hVΩ _ _ _ (hdv0 _),
    ← setIntegral_mul_restrictL2_extendL2 hΩm hVm hVΩ _ _ _ hv0]

end EllipticPdes.Regularity
