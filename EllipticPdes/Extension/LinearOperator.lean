/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Operator

/-!
# Extension operator as a linear map

Guo's proof produces an extension of each class. Evans states the same theorem as a bounded
linear operator, and this file packages it that way: the partition, the charts, the truncated
graphs, the radii and the cutoffs are all chosen from the domain alone, before any class appears,
so the assembled extension is a formula in the class, and every step of that formula is
multiplication by a fixed function, precomposition with a fixed map, or a finite sum. The map
`extOp` is built from those linear steps, so its linearity needs no proof.

The domain of the operator is the pair of a class and its gradient, which is what the weak
gradient of this development relates; the bound of clause (iii) is stated on that pair, so the
operator is bounded in the sense the theorem asserts at every exponent, and not only at `2`.

## Main declarations

* `EllipticPdes.Extension.extLinear`: the extension operator, as an `ℝ`-linear map.
* `EllipticPdes.Extension.extLinear_spec`: the three clauses of the theorem, stated for that
  map with a constant quantified before the class.
* `EllipticPdes.Extension.exists_extLinear`: the theorem as Evans states it, with the operator
  and the constant produced together.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1 (p. 253);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}

/-- **Extension operator.** A class and its gradient go to the extension and its gradient.
The partition, the charts, the graphs, the radii and the cutoff are fixed before the class, so
the map is linear. -/
def extLinear (P : BoundaryPartition d Ω) (χ : EuclideanSpace ℝ (Fin d) → ℝ) :
    SobolevPair d →ₗ[ℝ] SobolevPair d :=
  cutOp χ ∘ₗ extOp P

/-- The first component of `extLinear P χ w` is `extSubsetFun P χ w.1`. -/
@[simp] theorem extLinear_fst (P : BoundaryPartition d Ω)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    (extLinear P χ w).1 = extSubsetFun P χ w.1 := by
  simp only [extLinear, LinearMap.comp_apply, extOp_apply]
  rfl

/-- The gradient component of `extLinear P χ w` is `extSubsetGrad P χ w.1 w.2`. -/
@[simp] theorem extLinear_snd (P : BoundaryPartition d Ω)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (w : SobolevPair d) :
    (extLinear P χ w).2 = extSubsetGrad P χ w.1 w.2 := by
  simp only [extLinear, LinearMap.comp_apply, extOp_apply]
  rfl

/-- **Three clauses of the theorem for the operator.** The constant is quantified before
the class, so the map is bounded in the sense clause (iii) asserts. -/
theorem extLinear_spec (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (P : BoundaryPartition d Ω) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω')
    (hχ1 : ∀ y ∈ closure Ω, χ y = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ w : SobolevPair d,
      IntegrableOn w.1 Ω volume → (∀ k, IntegrableOn (w.2 k) Ω volume) →
      HasWeakGradOn Ω w.1 w.2 →
        HasWeakGradOn Set.univ (extLinear P χ w).1 (extLinear P χ w).2 ∧
          HasCompactSupport (extLinear P χ w).1 ∧ tsupport (extLinear P χ w).1 ⊆ Ω' ∧
          Integrable (extLinear P χ w).1 volume ∧
          (∀ k, Integrable ((extLinear P χ w).2 k) volume) ∧
          (∀ y ∈ Ω, (extLinear P χ w).1 y = w.1 y) ∧
          eLpNorm (extLinear P χ w).1 p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p
            (volume.restrict Ω) + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm ((extLinear P χ w).2 k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
              + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) := by
  obtain ⟨K, hK⟩ := extension_subset_bound hΩopen hΩb P hχc hχcs hχs hχ1 hp
  refine ⟨K, fun w hu hgi hwg => ?_⟩
  simp only [extLinear_fst, extLinear_snd]
  exact hK w.1 w.2 hu hgi hwg

/-- **Evans's extension operator** (§5.4 Theorem 1, p. 253). On a bounded domain with `C¹`
boundary, and for any open set the closure of the domain sits in, there is one `ℝ`-linear map
and one constant such that every class with a weak gradient on the domain goes to a class with
a weak gradient on the whole space, agreeing with it on the domain, supported inside that open
set, and bounded together with its gradient in every `Lᵖ` seminorm. -/
theorem exists_extLinear (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω')
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ (T : SobolevPair d →ₗ[ℝ] SobolevPair d) (K : ℝ≥0), ∀ w : SobolevPair d,
      IntegrableOn w.1 Ω volume → (∀ k, IntegrableOn (w.2 k) Ω volume) →
      HasWeakGradOn Ω w.1 w.2 →
        HasWeakGradOn Set.univ (T w).1 (T w).2 ∧
          HasCompactSupport (T w).1 ∧ tsupport (T w).1 ⊆ Ω' ∧
          Integrable (T w).1 volume ∧ (∀ k, Integrable ((T w).2 k) volume) ∧
          (∀ y ∈ Ω, (T w).1 y = w.1 y) ∧
          eLpNorm (T w).1 p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
            + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm ((T w).2 k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm w.1 p (volume.restrict Ω)
            + ∑ i, eLpNorm (w.2 i) p (volume.restrict Ω)) := by
  classical
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hclc : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset isClosed_closure
      (closure_minimal hRb isClosed_closedBall)
  obtain ⟨χ, hχc, hχcs, hχs, hχ1⟩ := exists_cutoff_one_on_compact hclc hΩ'open hsub
  obtain ⟨K, hK⟩ := extLinear_spec hΩopen hΩb P hχc hχcs hχs hχ1 hp
  exact ⟨extLinear P χ, K, hK⟩

end EllipticPdes.Extension
