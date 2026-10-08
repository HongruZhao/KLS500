/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.LocalExtension

/-!
# Gluing the local extensions

Guo's third step covers the boundary, fixes a partition of unity subordinate to that cover with
each support compactly inside its neighbourhood, and sets `ū = ∑ᵢ Pᵢ ūᵢ`. This file carries out
that sum.

Each piece is a local extension cut down by its piece of the partition, so the cutoff comes
after the extension. That order is what makes the sum agree with the class: where a piece of the
partition is nonzero the point lies in that chart's ball, where the local extension agrees with
the class, so the piece equals `Pᵢ u` there and off the ball both sides vanish. The pieces then
add to `u` because the partition adds to one. Every piece is a linear map on pairs of a class and
a gradient, so the sum is.

The support clause follows by one more cutoff, which is how Guo reaches it: any open set the
closure of the domain sits in admits a smooth cutoff equal to one on that closure, and
multiplying by it moves the support inside without disturbing the agreement.

## Constant of clause (iii)

The partition, the charts, the radii and the supremum of each piece and of its partials all
depend on the domain alone, so `extension_bound` fixes them before the class appears and sums
the local constants of `localExtension_bound` over the finitely many pieces. That is clause
(iii): one constant, depending on the domain and the exponent, bounding the extension and its
gradient by the class and its gradient over the domain.

## Main declarations

* `EllipticPdes.Extension.extOp`: the glued extension, as a linear map on pairs.
* `EllipticPdes.Extension.extension_bound`: the class extends across the whole boundary, with a
  constant taken before the class.
* `EllipticPdes.Extension.exists_extension_bound`: the same with the partition quantified away.
* `EllipticPdes.Extension.exists_cutoff_one_on_compact`: a smooth cutoff between a compact set
  and an open one.
* `EllipticPdes.Extension.extension_subset_bound`: the three clauses of the theorem.
* `EllipticPdes.Extension.exists_extension_subset`: clauses (i) and (ii).

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 22); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn hasWeakGradOn_finsetSum)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The pieces and their sum -/

/-- **One piece of the glued extension, as a linear map on pairs.** The interior piece is the
pair cut down by its piece of the partition; a boundary piece is the local extension of its
chart, cut down the same way. The cutoff comes after the extension, which is what makes the
piece agree with `Pᵢ u` on the domain. -/
def extPieceOp {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω) :
    Option {x // x ∈ P.centres} → SobolevPair d →ₗ[ℝ] SobolevPair d
  | none => cutOp (P.part none)
  | some x => cutOp (P.part (some x)) ∘ₗ
      localOp (P.chart x) (chartGraph (P.chart x) x)
        (chartBump (x : EuclideanSpace ℝ (Fin d)) (P.chart x).radius_pos (P.radius_lt x))

/-- **Glued extension, as a linear map on pairs.** The pieces add to the class on the domain
because the partition adds to one there. -/
def extOp {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω) :
    SobolevPair d →ₗ[ℝ] SobolevPair d :=
  ∑ i : Option {x // x ∈ P.centres}, extPieceOp P i

/-- **Glued extension.** -/
def extFun {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (extOp P (u, 0)).1

/-- **Gradient of the glued extension.** -/
def extFunGrad {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
  (extOp P (u, g)).2

/-- The glued extension is, as a function, the sum of the pieces. -/
theorem extOp_fst {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (w : SobolevPair d) :
    (extOp P w).1 = fun y => ∑ i, (extPieceOp P i w).1 y := by
  funext y
  simp [extOp, Prod.fst_sum, Finset.sum_apply]

/-- The gradient of the glued extension is, as a function, the sum of the pieces. -/
theorem extOp_snd {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (w : SobolevPair d) (k : Fin d) :
    (extOp P w).2 k = fun y => ∑ i, (extPieceOp P i w).2 k y := by
  funext y
  simp [extOp, Prod.snd_sum, Finset.sum_apply]

/-- `extOp` is the pair of `extFun` and `extFunGrad`. -/
theorem extOp_apply {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (w : SobolevPair d) : extOp P w = (extFun P w.1, extFunGrad P w.1 w.2) := by
  refine Prod.ext ?_ rfl
  unfold extFun
  rw [extOp_fst, extOp_fst]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  cases i <;> rfl

/-- **Bound for one piece of the glued extension.** The constant depends on the piece and on
the exponent alone. -/
theorem extPieceOp_bound {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (P : BoundaryPartition d Ω)
    (i : Option {x // x ∈ P.centres}) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ Ki : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
        HasWeakGradOn Set.univ (extPieceOp P i (u, g)).1 (extPieceOp P i (u, g)).2 ∧
          Integrable (extPieceOp P i (u, g)).1 volume ∧
          (∀ k, Integrable ((extPieceOp P i (u, g)).2 k) volume) ∧
          (∀ y ∈ Ω, (extPieceOp P i (u, g)).1 y = P.part i y * u y) ∧
          eLpNorm (extPieceOp P i (u, g)).1 p volume
            ≤ (Ki : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g ∧
          ∀ k, eLpNorm ((extPieceOp P i (u, g)).2 k) p volume
            ≤ (Ki : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g := by
  rcases i with _ | x
  · obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    have hcs : HasCompactSupport (P.part none) :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset
        (isClosed_tsupport _) (P.part_interior.trans hRb)
    obtain ⟨C, -, hC, hCd⟩ := exists_bound_with_partials (P.part_contDiff none) hcs
    refine ⟨Real.toNNReal C, fun u g hu hgi hwg => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := cutOp_global hΩopen.measurableSet (P.part_contDiff none) hcs
      P.part_interior hC hCd hp hu hgi hwg (N := pairNorm p (volume.restrict Ω) u g)
      (K₁ := 1) (K₂ := 1) (by simpa using eLpNorm_le_pairNorm)
      (fun k => by simpa using eLpNorm_add_grad_le_pairNorm k)
    simp only [one_mul] at h4 h5
    exact ⟨h1, h2, h3, fun y _ => rfl, h4, h5⟩
  · have hcs := P.hasCompactSupport_part_some x
    obtain ⟨Kx, hKx⟩ := localExtension_bound (P.chart x) hΩopen.measurableSet
      (P.chart_fits x x.2) (P.radius_lt x) hp
    obtain ⟨C, -, hC, hCd⟩ := exists_bound_with_partials (P.part_contDiff (some x)) hcs
    refine ⟨Real.toNNReal C * (2 * Kx), fun u g hu hgi hwg => ?_⟩
    obtain ⟨hw, hI, hgI, hag, hb1, hb2⟩ := hKx u g hu hgi hwg
    replace hb1 : eLpNorm (localExt (P.chart x) x (P.radius_lt x) u) p volume
        ≤ Kx * pairNorm p (volume.restrict Ω) u g := hb1
    replace hb2 : ∀ k, eLpNorm (localExtGrad (P.chart x) x (P.radius_lt x) u g k) p volume
        ≤ Kx * pairNorm p (volume.restrict Ω) u g := hb2
    have hrestr : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
        eLpNorm w p (volume.restrict (ball (x : EuclideanSpace ℝ (Fin d)) (P.radius x)))
          ≤ eLpNorm w p volume := fun w =>
      eLpNorm_mono_measure w Measure.restrict_le_self
    obtain ⟨h1, h2, h3, h4, h5⟩ := cutOp_global measurableSet_ball (P.part_contDiff (some x))
      hcs (P.part_boundary x) hC hCd hp hI.integrableOn (fun k => (hgI k).integrableOn) hw
      (N := pairNorm p (volume.restrict Ω) u g) (K₁ := Kx) (K₂ := 2 * Kx)
      ((hrestr _).trans hb1) fun k => ((add_le_add ((hrestr _).trans hb1)
        ((hrestr _).trans (hb2 k))).trans_eq (by ring))
    have hK : ((Real.toNNReal C * (2 * Kx) : ℝ≥0) : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g
        = ENNReal.ofReal C * (2 * Kx * pairNorm p (volume.restrict Ω) u g) := by
      rw [ENNReal.ofReal]
      push_cast
      ring
    refine ⟨h1, h2, h3, fun y hy => ?_, ?_, fun k => ?_⟩
    · by_cases hyb : y ∈ ball (x : EuclideanSpace ℝ (Fin d)) (P.radius x)
      · change P.part (some x) y * localExt (P.chart x) x (P.radius_lt x) u y = _
        rw [hag y ⟨hy, hyb⟩]
      · change P.part (some x) y * localExt (P.chart x) x (P.radius_lt x) u y = _
        rw [image_eq_zero_of_notMem_tsupport fun hc => hyb (P.part_boundary x hc), zero_mul,
          zero_mul]
    · refine h4.trans ?_
      rw [hK]
      gcongr
      exact le_mul_of_one_le_left zero_le one_le_two
    · rw [hK]
      exact (h5 k).trans_eq (by rw [mul_assoc])

/-- **Guo's third step with its constant** (Theorem III.2.2, proof step 3, p. 22): the local
extensions glued with the partition of unity extend the class across the whole boundary, and one
constant, taken before the class, bounds the extension and its gradient by the class and its
gradient over the domain. -/
theorem extension_bound {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (P : BoundaryPartition d Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
        HasWeakGradOn Set.univ (extFun P u) (extFunGrad P u g) ∧
          Integrable (extFun P u) volume ∧
          (∀ k, Integrable (extFunGrad P u g k) volume) ∧
          (∀ y ∈ Ω, extFun P u y = u y) ∧
          eLpNorm (extFun P u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (extFunGrad P u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  classical
  choose Ki hKi using fun i => extPieceOp_bound hΩopen hΩb P i hp
  refine ⟨∑ i, Ki i, fun u g hu hgi hwg => ?_⟩
  have hpiece := fun i => hKi i u g hu hgi hwg
  have hF : extFun P u = fun y => ∑ i, (extPieceOp P i (u, g)).1 y :=
    (congrArg Prod.fst (extOp_apply P (u, g))).symm.trans (extOp_fst P (u, g))
  have hG : ∀ k, extFunGrad P u g k = fun y => ∑ i, (extPieceOp P i (u, g)).2 k y :=
    fun k => extOp_snd P (u, g) k
  have hbound : ∀ w : Option {x // x ∈ P.centres} → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, eLpNorm (w i) p volume ≤ (Ki i : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g) →
      eLpNorm (fun y => ∑ i, w i y) p volume
        ≤ ((∑ i, Ki i : ℝ≥0) : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g := fun w hw => by
    have hsum : (fun y => ∑ i, w i y) = ∑ i, w i := by funext y; rw [Finset.sum_apply]
    rw [hsum]
    refine (eLpNorm_sum_le hp).trans ((Finset.sum_le_sum fun i _ => hw i).trans_eq ?_)
    rw [← Finset.sum_mul, ENNReal.ofNNReal_finsetSum]
  rw [hF, funext hG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hasWeakGradOn_finsetSum Finset.univ (fun i _ => (hpiece i).2.1.integrableOn)
      (fun i _ k => (hpiece i).2.2.1 k |>.integrableOn) (fun i _ => (hpiece i).1)
  · exact integrable_finsetSum _ fun i _ => (hpiece i).2.1
  · exact fun k => integrable_finsetSum _ fun i _ => (hpiece i).2.2.1 k
  · intro y hy
    calc (∑ i, (extPieceOp P i (u, g)).1 y) = ∑ i, P.part i y * u y :=
          Finset.sum_congr rfl fun i _ => (hpiece i).2.2.2.1 y hy
      _ = u y := by rw [← Finset.sum_mul, P.part_sum y (subset_closure hy), one_mul]
  · exact hbound _ fun i => (hpiece i).2.2.2.2.1
  · exact fun k => hbound _ fun i => (hpiece i).2.2.2.2.2 k

/-- **Guo's third step with its constant**, with the partition and the extension quantified
away. This is the form the support clause and the embedding consume. -/
theorem exists_extension_bound (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn Set.univ U G ∧ Integrable U volume ∧
          (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨K, hK⟩ := extension_bound hΩopen hΩb P hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **Guo's third step** (Theorem III.2.2, proof step 3, p. 22): the local extensions glued with
the partition of unity extend the class across the whole boundary. -/
theorem exists_extension (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  obtain ⟨K, hK⟩ := exists_extension_bound hd hΩopen hΩb hC1 (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hUint, hGint, hag⟩

/-- **Cutting between a compact set and an open one.** A smooth cutoff equal to one on the
compact set and compactly supported inside the open one. -/
theorem exists_cutoff_one_on_compact {K U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ y ∈ K, χ y = 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf, -, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_interior (s := L)) hK.isClosed hKL
  have hts : tsupport f ⊆ L := by
    rw [tsupport, hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  exact ⟨f, hf, hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLU,
    fun y hy => (h1 y).1 hy⟩

/-- **Extension with its support cut into a given open set.** One more cutoff, equal to
one on the closure of the domain, which leaves the agreement alone and moves the support. -/
def extSubsetFun {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => χ y * extFun P u y

/-- **Gradient of that extension**, with the cutoff's own derivative. -/
def extSubsetGrad {Ω : Set (EuclideanSpace ℝ (Fin d))} (P : BoundaryPartition d Ω)
    (χ u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => χ y * extFunGrad P u g k y + partialD k χ y * extFun P u y

/-- **Guo's Theorem III.2.2** (p. 20), all three clauses. The extension agrees with the class on
the domain, is supported inside any open set the closure of the domain sits in, and is bounded
in every `Lᵖ` seminorm, together with its gradient, by the class and its gradient over the
domain, with one constant taken before the class. -/
theorem extension_subset_bound {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (P : BoundaryPartition d Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω')
    (hχ1 : ∀ y ∈ closure Ω, χ y = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
        HasWeakGradOn Set.univ (extSubsetFun P χ u) (extSubsetGrad P χ u g) ∧
          HasCompactSupport (extSubsetFun P χ u) ∧ tsupport (extSubsetFun P χ u) ⊆ Ω' ∧
          Integrable (extSubsetFun P χ u) volume ∧
          (∀ k, Integrable (extSubsetGrad P χ u g k) volume) ∧
          (∀ y ∈ Ω, extSubsetFun P χ u y = u y) ∧
          eLpNorm (extSubsetFun P χ u) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (extSubsetGrad P χ u g k) p volume
            ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
              + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨K₀, hK₀⟩ := extension_bound hΩopen hΩb P hp
  obtain ⟨C, -, hC, hCd⟩ := exists_bound_with_partials hχc hχcs
  refine ⟨Real.toNNReal C * (2 * K₀), fun u g hu hgi hwg => ?_⟩
  obtain ⟨hwg0, hint0, hgint0, hag0, hUb0, hGb0⟩ := hK₀ u g hu hgi hwg
  replace hUb0 : eLpNorm (extFun P u) p volume ≤ K₀ * pairNorm p (volume.restrict Ω) u g := hUb0
  replace hGb0 : ∀ k, eLpNorm (extFunGrad P u g k) p volume
      ≤ K₀ * pairNorm p (volume.restrict Ω) u g := hGb0
  have hrestr : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
      eLpNorm w p (volume.restrict Set.univ) ≤ eLpNorm w p volume := fun w => by
    rw [Measure.restrict_univ]
  obtain ⟨h1, h2, h3, h4, h5⟩ := cutOp_global MeasurableSet.univ hχc hχcs (Set.subset_univ _)
    hC hCd hp hint0.integrableOn (fun k => (hgint0 k).integrableOn) (by simpa using hwg0)
    (N := pairNorm p (volume.restrict Ω) u g) (K₁ := K₀) (K₂ := 2 * K₀)
    ((hrestr _).trans hUb0) fun k => ((add_le_add ((hrestr _).trans hUb0)
      ((hrestr _).trans (hGb0 k))).trans_eq (by ring))
  have hK : ((Real.toNNReal C * (2 * K₀) : ℝ≥0) : ℝ≥0∞) * pairNorm p (volume.restrict Ω) u g
      = ENNReal.ofReal C * (2 * K₀ * pairNorm p (volume.restrict Ω) u g) := by
    rw [ENNReal.ofReal]
    push_cast
    ring
  refine ⟨h1, hχcs.mul_right, (tsupport_mul_subset_left).trans hχs, h2, h3,
    fun y hy => ?_, ?_, fun k => ?_⟩
  · change χ y * extFun P u y = u y
    rw [hχ1 y (subset_closure hy), one_mul, hag0 y hy]
  · exact h4.trans ((mul_le_mul_right (by gcongr; exact le_mul_of_one_le_left zero_le one_le_two)
      _).trans_eq hK.symm)
  · exact (h5 k).trans_eq hK.symm

/-- **Guo's Theorem III.2.2** (p. 20), all three clauses, with the partition, the cutoff and
the extension quantified away. -/
theorem exists_extension_subset_bound (hd : 0 < d) {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω') {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) → HasWeakGradOn Ω u g →
      ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn Set.univ U G ∧ HasCompactSupport U ∧ tsupport U ⊆ Ω' ∧
          Integrable U volume ∧ (∀ k, Integrable (G k) volume) ∧ (∀ y ∈ Ω, U y = u y) ∧
          eLpNorm U p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) ∧
          ∀ k, eLpNorm (G k) p volume ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
            + ∑ i, eLpNorm (g i) p (volume.restrict Ω)) := by
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hclc : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset isClosed_closure
      (closure_minimal hRb (isClosed_closedBall))
  obtain ⟨χ, hχc, hχcs, hχs, hχ1⟩ := exists_cutoff_one_on_compact hclc hΩ'open hsub
  obtain ⟨K, hK⟩ := extension_subset_bound hΩopen hΩb P hχc hχcs hχs hχ1 hp
  refine ⟨K, fun u g hu hgi hwg => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hK u g hu hgi hwg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **Clauses (i) and (ii) of Guo's Theorem III.2.2** (p. 20). The extension agrees with the class
on the domain and is supported inside any open set the closure of the domain sits in. -/
theorem exists_extension_subset (hd : 0 < d) {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ HasCompactSupport U ∧ tsupport U ⊆ Ω' ∧
        Integrable U volume ∧ (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  obtain ⟨K, hK⟩ :=
    exists_extension_subset_bound hd hΩopen hΩb hC1 hΩ'open hsub (p := 1) le_rfl
  obtain ⟨U, G, hwgU, hcsU, hsuppU, hUint, hGint, hag, -, -⟩ := hK u g hu hgi hwg
  exact ⟨U, G, hwgU, hcsU, hsuppU, hUint, hGint, hag⟩

end EllipticPdes.Extension
