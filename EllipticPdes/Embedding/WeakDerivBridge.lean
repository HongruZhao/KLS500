/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.CoeffWkInfty

/-!
# Bridges between the weak-derivative predicates

Every weak-derivative predicate of the development is an instance of
`EllipticPdes.HasWeakLineDerivOn` (one direction) or `EllipticPdes.HasWeakFDerivOn` (all
directions), under the local integrability those carry:

* `HasWeakGradOn` is `HasWeakFDerivOn` with derivative `gradCLM g`
  (`EllipticPdes.Embedding.hasWeakGradOn_iff_hasWeakFDerivOn`, in `Embedding/WeakGradient`);
* `HasWeakDerivAlong` is `HasWeakLineDerivOn`
  (`EllipticPdes.Embedding.hasWeakDerivAlong_iff_hasWeakLineDerivOn`, same file);
* the `L²` predicates `Regularity.HasWeakDerivOn` and `Regularity.HasWeakDeriv`, and the pointwise
  `Regularity.HasWeakPartial`, are `HasWeakDerivAlong` along a coordinate direction, on the set
  and on the whole space respectively (this file).


The `L²` weak derivatives produced by `interior_H2_estimate` are pointwise weak
gradients in the sense of the embedding layer, so the Morrey inequality consumes them
directly at `p = 2`, hence in dimension one.

Higher dimensions need an `Lᵖ` bootstrap first, since Morrey asks for `p > d`. Dimensions two and
three are covered in `EllipticPdes.Embedding.GagliardoNirenberg`, where the
Gagliardo-Nirenberg-Sobolev inequality raises the gradient from `L²` to `L⁶` at `d = 3` and, over
the finite measure of a ball, from `L^{4/3}` to `L⁴` at `d = 2`. The three resulting Hölder
estimates are `EllipticPdes.Embedding.interior_holder_estimate_one`,
`EllipticPdes.Embedding.interior_holder_estimate_two` and
`EllipticPdes.Embedding.interior_holder_estimate`.

Dimension four and above needs the step iterated, which uses a weak derivative per rung and so
asks for more than the `H²` estimate supplies. `EllipticPdes.Embedding.memLp_of_gradClosed` runs
that ladder on a family closed under differentiation.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- An `L²` weak gradient (componentwise `HasWeakDerivOn`) is a pointwise weak
gradient. This connects `interior_H2_estimate`'s output into `morrey_ball`. -/
theorem hasWeakGradOn_of_hasWeakDerivOn {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : Lp ℝ 2 (volume.restrict B)} {g : Fin d → Lp ℝ 2 (volume.restrict B)}
    (h : ∀ k, EllipticPdes.Regularity.HasWeakDerivOn B k u (g k)) :
    HasWeakGradOn B (fun x => (u x : ℝ)) (fun k x => (g k x : ℝ)) := by
  intro φ hφc hφcs hφB k
  exact h k φ hφc hφcs hφB

open EllipticPdes.Regularity (HasWeakDeriv HasWeakDerivOn HasWeakPartial)

/-- `HasWeakDerivOn V k` is the weak derivative along the `k`-th coordinate direction on `V`. -/
theorem hasWeakDerivOn_iff_hasWeakDerivAlong {V : Set (EuclideanSpace ℝ (Fin d))} {k : Fin d}
    {g g' : Lp ℝ 2 (volume.restrict V)} :
    HasWeakDerivOn V k g g' ↔ HasWeakDerivAlong volume (EuclideanSpace.single k 1) V g g' :=
  Iff.rfl

/-- An `L²(V)` class is locally integrable on `V`. -/
theorem locallyIntegrableOn_of_Lp {V : Set (EuclideanSpace ℝ (Fin d))}
    (g : Lp ℝ 2 (volume.restrict V)) : LocallyIntegrableOn g V volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable one_le_two)

/-- **`HasWeakDerivOn` is `HasWeakLineDerivOn`.** On an open set `V`, the `L²` weak
`k`-derivative is the weak derivative along `EuclideanSpace.single k 1` of
`EllipticPdes.HasWeakLineDerivOn`. -/
theorem hasWeakDerivOn_iff_hasWeakLineDerivOn {V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsOpen V) {k : Fin d} {g g' : Lp ℝ 2 (volume.restrict V)} :
    HasWeakDerivOn V k g g' ↔ HasWeakLineDerivOn ⟨V, hV⟩ (EuclideanSpace.single k 1) g g' :=
  hasWeakDerivAlong_iff_hasWeakLineDerivOn hV (locallyIntegrableOn_of_Lp g)
    (locallyIntegrableOn_of_Lp g')

/-- `HasWeakPartial k` is the weak derivative along the `k`-th coordinate direction on the whole
space. -/
theorem hasWeakPartial_iff_hasWeakDerivAlong {k : Fin d}
    {f f' : EuclideanSpace ℝ (Fin d) → ℝ} :
    HasWeakPartial k f f' ↔ HasWeakDerivAlong volume (EuclideanSpace.single k 1) univ f f' := by
  simp only [HasWeakPartial, HasWeakDerivAlong, Measure.restrict_univ, subset_univ,
    forall_const]
  rfl

/-- **`HasWeakPartial` is `HasWeakLineDerivOn`.** For locally integrable `f` and `f'`, the weak
`k`-th partial derivative is the weak derivative on the whole space along
`EuclideanSpace.single k 1`. -/
theorem hasWeakPartial_iff_hasWeakLineDerivOn {k : Fin d} {f f' : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrable f volume) (hf' : LocallyIntegrable f' volume) :
    HasWeakPartial k f f' ↔
      HasWeakLineDerivOn ⟨univ, isOpen_univ⟩ (EuclideanSpace.single k 1) f f' := by
  rw [hasWeakPartial_iff_hasWeakDerivAlong]
  exact hasWeakDerivAlong_iff_hasWeakLineDerivOn isOpen_univ (hf.locallyIntegrableOn _)
    (hf'.locallyIntegrableOn _)

/-- `HasWeakDeriv k` is `HasWeakPartial k` for the representatives of the classes. -/
theorem hasWeakDeriv_iff_hasWeakPartial {k : Fin d} {g g' : EucL2 d} :
    HasWeakDeriv k g g' ↔ HasWeakPartial k g g' :=
  Iff.rfl

/-- **`HasWeakDeriv` is `HasWeakLineDerivOn`.** The whole-space `L²` weak `k`-derivative is the
weak derivative on the whole space along `EuclideanSpace.single k 1`. -/
theorem hasWeakDeriv_iff_hasWeakLineDerivOn {k : Fin d} {g g' : EucL2 d} :
    HasWeakDeriv k g g' ↔
      HasWeakLineDerivOn ⟨univ, isOpen_univ⟩ (EuclideanSpace.single k 1) g g' :=
  hasWeakPartial_iff_hasWeakLineDerivOn ((Lp.memLp g).locallyIntegrable one_le_two)
    ((Lp.memLp g').locallyIntegrable one_le_two)

end EllipticPdes.Embedding
