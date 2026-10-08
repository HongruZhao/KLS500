/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Sobolev.WeakDerivClassical

/-!
# Continuous weak gradient as a classical gradient

The Sobolev ladder puts a solution and its weak derivatives in a Hölder class, so both are
continuous. Continuity is what turns them back into classical derivatives: a function with a
continuous weak gradient on an open set is Fréchet differentiable there, with that gradient.

The statement here is the coordinate form, on `EuclideanSpace ℝ (Fin d)`, of
`EllipticPdes.HasWeakFDerivOn.hasFDerivAt`, which holds on any finite-dimensional real normed
space for any Banach-valued function: a gradient tuple `g` is read as the functional
`gradCLM g`, the Riesz dual of `(g k ·)ₖ`, and `hasWeakGradOn_iff_hasWeakFDerivOn` identifies
the two notions of weak derivative.

## Main declarations

* `EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`: the classical derivative.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Continuous weak gradient as a classical derivative.** On an open region, a function that
is continuous and integrable, with a weak gradient that is continuous and integrable, is Fréchet
differentiable at every point, with derivative the functional the gradient names. This is
`EllipticPdes.HasWeakFDerivOn.hasFDerivAt` through `hasWeakGradOn_iff_hasWeakFDerivOn`. -/
theorem hasFDerivAt_of_continuousOn_hasWeakGradOn
    {B : Set (EuclideanSpace ℝ (Fin d))} (_hBm : MeasurableSet B) (hBo : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hui : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (huc : ContinuousOn u B) (hgc : ∀ k, ContinuousOn (g k) B)
    (hw : HasWeakGradOn B u g) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ B) :
    HasFDerivAt u (gradCLM g x) x :=
  ((hasWeakGradOn_iff_hasWeakFDerivOn hBo hui.locallyIntegrableOn
    fun k => (hgi k).locallyIntegrableOn).1 hw).hasFDerivAt huc (continuousOn_gradCLM hgc) hx

end EllipticPdes.Embedding
