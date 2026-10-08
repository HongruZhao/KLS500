/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient

/-!
# Uniqueness of the weak gradient on an open set

Two weak gradients of one function differ by a function orthogonal to every test function, and
on an open set the fundamental lemma of the calculus of variations kills it. The statements here
are the coordinate forms of `EllipticPdes.Embedding.HasWeakDerivAlong.ae_eq`, which rests on
`EllipticPdes.ae_eq_of_forall_integral_smul_eq` (Mathlib's `Distribution.ofFun_injective`).

Uniqueness is what lets separate structures be assembled into one family. Higher interior
regularity is proved order by order, so a solution with derivatives of every order arrives as one
family per order, with nothing relating them; uniqueness identifies the entries they share, and
a single family closed under differentiation follows.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_unique_ae_of_locallyIntegrableOn`: two locally
  integrable weak gradients of one function agree almost everywhere on an open set.
* `EllipticPdes.Embedding.hasWeakGradOn_unique_ae`: the same for gradients integrable on a ball.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability against a test factor.** A locally integrable class on a set, times a
continuous function with compact support inside the set, is integrable on the whole space. -/
theorem integrable_mul_of_locallyIntegrableOn {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hs : tsupport h ⊆ Ω) :
    Integrable (fun x => u x * h x) volume := by
  simpa [mul_comm] using hu.integrable_smul_of_tsupport_subset hc hcs hs

/-- **Uniqueness of the weak gradient on an open set**, with local integrability. Each component
is `HasWeakDerivAlong.ae_eq`. -/
theorem hasWeakGradOn_unique_ae_of_locallyIntegrableOn
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, LocallyIntegrableOn (g k) Ω volume)
    (hg' : ∀ k, LocallyIntegrableOn (g' k) Ω volume)
    (h : HasWeakGradOn Ω u g) (h' : HasWeakGradOn Ω u g') (k : Fin d) :
    g k =ᵐ[volume.restrict Ω] g' k :=
  HasWeakDerivAlong.ae_eq hΩ (hg k) (hg' k) (hasWeakGradOn_iff.1 h k) (hasWeakGradOn_iff.1 h' k)

/-- **Uniqueness of the weak gradient on an open set.** Two weak gradients of the same function
agree almost everywhere, given integrability on the set. -/
theorem hasWeakGradOn_unique_ae {B : Set (EuclideanSpace ℝ (Fin d))} (hBo : IsOpen B)
    (_hBm : MeasurableSet B) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, IntegrableOn (g k) B volume) (hg' : ∀ k, IntegrableOn (g' k) B volume)
    (h : HasWeakGradOn B u g) (h' : HasWeakGradOn B u g') (k : Fin d) :
    g k =ᵐ[volume.restrict B] g' k :=
  hasWeakGradOn_unique_ae_of_locallyIntegrableOn hBo (fun k => (hg k).locallyIntegrableOn)
    (fun k => (hg' k).locallyIntegrableOn) h h' k

end EllipticPdes.Embedding
