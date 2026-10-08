/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Operator

/-!
# Gagliardo-Nirenberg-Sobolev on a bounded domain

`EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le` raises the exponent from `p` to the
Sobolev conjugate on a ball inside a ball, the inner ball being where the cutoff feeding the
whole-space inequality is one. On a bounded domain with `C¹` boundary no ball shrinks:
`EllipticPdes.Extension.exists_extension_bound` puts the class on the whole space with a bound
by its seminorms over the domain, the whole-space inequality applies there, and the conclusion
restricts back to the domain.

This is the single rung the proof of the Sobolev embedding at order `k` iterates.

## Main declarations

* `EllipticPdes.Embedding.isFiniteMeasure_restrict_of_isBounded`: a bounded domain has finite
  measure.
* `EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain`: the rung on the domain, with a
  constant taken before the class.
* `EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain_of_le`: the same rung fed by data
  at a higher exponent.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.4.3 and
Theorem IV.2.3; L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Theorem 2.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary exists_extension_bound)

variable {d : ℕ}

/-- **Finite measure of a bounded domain.** Lowering an exponent on it uses this. -/
theorem isFiniteMeasure_restrict_of_isBounded {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩb : Bornology.IsBounded Ω) : IsFiniteMeasure (volume.restrict Ω) :=
  isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne

/-- **Two balls around a bounded set.** The closure of a bounded set lies in a ball about the
origin, and a larger concentric ball contains a point outside the smaller one. -/
theorem exists_balls_around_isBounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {Ω : Set E} (hΩ : Bornology.IsBounded Ω) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ closure Ω ⊆ ball (0 : E) r ∧ ∃ z ∈ ball (0 : E) R, z ∉ ball 0 r := by
  obtain ⟨R₀, hR₀⟩ := hΩ.subset_closedBall (0 : E)
  have habs : (0 : ℝ) ≤ |R₀| := abs_nonneg R₀
  obtain ⟨z, hz⟩ := exists_norm_eq E (show (0 : ℝ) ≤ |R₀| + 3 / 2 by linarith)
  refine ⟨|R₀| + 1, |R₀| + 2, by linarith, by linarith, ?_, z, ?_, ?_⟩
  · refine (closure_minimal hR₀ isClosed_closedBall).trans (closedBall_subset_ball ?_)
    linarith [le_abs_self R₀]
  · rw [mem_ball_zero_iff, hz]; linarith
  · rw [mem_ball_zero_iff, hz, not_lt]; linarith

/-- **Gagliardo-Nirenberg-Sobolev on a bounded domain with `C¹` boundary.** A class on `Ω`
with an `Lᵖ` weak gradient lies in `L^{p'}(Ω)` at the Sobolev conjugate
`1/p' = 1/p - 1/d`, with one constant, depending on the domain, the dimension and the exponents
alone, bounding it by the class and its gradient over the domain. -/
theorem exists_eLpNorm_sobolevConj_le_domain (hd : 0 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p p' : ℝ≥0} (hp : 1 ≤ p)
    (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp u p (volume.restrict Ω) → (∀ k, MemLp (g k) p (volume.restrict Ω)) →
      HasWeakGradOn Ω u g →
      MemLp u p' (volume.restrict Ω) ∧
        eLpNorm u p' (volume.restrict Ω) ≤ (K : ℝ≥0∞) * (eLpNorm u p (volume.restrict Ω)
          + ∑ k, eLpNorm (g k) p (volume.restrict Ω)) := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; exact hd)
  obtain ⟨r, R, hr, hrR, hcl, -⟩ := exists_balls_around_isBounded hΩb
  have hΩr : Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) r := subset_closure.trans hcl
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨K₀, hK₀⟩ := exists_extension_bound hd hΩopen hΩb hC1 (p := (p : ℝ≥0∞)) hp1
  obtain ⟨K₁, hK₁⟩ :=
    exists_eLpNorm_sobolevConj_le hd (0 : EuclideanSpace ℝ (Fin d)) hp hpp' hr hrR
  refine ⟨K₁ * (((d + 1 : ℕ) : ℝ≥0) * K₀), ?_⟩
  have hKcoe : ((K₁ * (((d + 1 : ℕ) : ℝ≥0) * K₀) : ℝ≥0) : ℝ≥0∞)
      = (K₁ : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (K₀ : ℝ≥0∞)) := by
    push_cast
    ring
  rw [hKcoe]
  intro u g hmu hmg hwg
  set N : ℝ≥0∞ := eLpNorm u (p : ℝ≥0∞) (volume.restrict Ω)
    + ∑ k, eLpNorm (g k) (p : ℝ≥0∞) (volume.restrict Ω) with hNdef
  have hNfin : N < ⊤ := by
    rw [hNdef]
    exact ENNReal.add_lt_top.mpr ⟨hmu.eLpNorm_lt_top,
      ENNReal.sum_lt_top.mpr fun k _ => (hmg k).eLpNorm_lt_top⟩
  -- the class, extended to the whole space with its bound
  obtain ⟨U, G, hwgU, hUint, hGint, hag, hUb, hGb⟩ :=
    hK₀ u g (hmu.integrable hp1) (fun k => (hmg k).integrable hp1) hwg
  have hbnd : (K₀ : ℝ≥0∞) * N < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hNfin
  have hMU : MemLp U (p : ℝ≥0∞) volume := lt_of_le_of_lt hUb hbnd
  have hMG : ∀ k, MemLp (G k) (p : ℝ≥0∞) volume :=
    fun k => lt_of_le_of_lt (hGb k) hbnd
  obtain ⟨-, hbdU⟩ := hK₁ U G (hMU.restrict _) (fun k => (hMG k).restrict _)
    (hwgU.mono (Set.subset_univ _))
  have hMemU : MemLp U (p' : ℝ≥0∞) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) r)) :=
    (hK₁ U G (hMU.restrict _) (fun k => (hMG k).restrict _)
      (hwgU.mono (Set.subset_univ _))).1
  -- the two agree on the domain
  have hue : u =ᵐ[volume.restrict Ω] U :=
    (ae_restrict_iff' hΩopen.measurableSet).mpr
      (Filter.Eventually.of_forall fun y hy => (hag y hy).symm)
  have hUΩ : MemLp U (p' : ℝ≥0∞) (volume.restrict Ω) :=
    hMemU.mono_measure (Measure.restrict_mono hΩr le_rfl)
  refine ⟨hUΩ.ae_eq hue.symm, ?_⟩
  -- the whole-space seminorms, read back against the domain
  have hUpiece : eLpNorm U (p : ℝ≥0∞)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R)) ≤ (K₀ : ℝ≥0∞) * N :=
    le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) hUb
  have hGpiece : ∑ k, eLpNorm (G k) (p : ℝ≥0∞)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R))
      ≤ (d : ℝ≥0∞) * ((K₀ : ℝ≥0∞) * N) := by
    calc ∑ k, eLpNorm (G k) (p : ℝ≥0∞)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R))
        ≤ ∑ _k : Fin d, (K₀ : ℝ≥0∞) * N :=
          Finset.sum_le_sum fun k _ =>
            le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) (hGb k)
      _ = (d : ℝ≥0∞) * ((K₀ : ℝ≥0∞) * N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc eLpNorm u (p' : ℝ≥0∞) (volume.restrict Ω)
      = eLpNorm U (p' : ℝ≥0∞) (volume.restrict Ω) := eLpNorm_congr_ae hue
    _ ≤ eLpNorm U (p' : ℝ≥0∞)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) r)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hΩr le_rfl)
    _ ≤ (K₁ : ℝ≥0∞) * (eLpNorm U (p : ℝ≥0∞)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R))
          + ∑ k, eLpNorm (G k) (p : ℝ≥0∞)
              (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) R))) := hbdU
    _ ≤ (K₁ : ℝ≥0∞) * ((K₀ : ℝ≥0∞) * N + (d : ℝ≥0∞) * ((K₀ : ℝ≥0∞) * N)) :=
        mul_le_mul_right (add_le_add hUpiece hGpiece) _
    _ = (K₁ : ℝ≥0∞) * (((d : ℝ≥0∞) + 1) * (K₀ : ℝ≥0∞)) * N := by ring

/-- **Rung fed by a higher exponent.** A bounded domain has finite measure, so `Lq` data
with `p ≤ q` is `Lᵖ` data, at the price of a factor `|Ω|^{1/p - 1/q}` the constant absorbs. This
is the form the ladder consumes at every rung above the first. -/
theorem exists_eLpNorm_sobolevConj_le_domain_of_le (hd : 0 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p q p' : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp u q (volume.restrict Ω) → (∀ k, MemLp (g k) q (volume.restrict Ω)) →
      HasWeakGradOn Ω u g →
      MemLp u p' (volume.restrict Ω) ∧
        eLpNorm u p' (volume.restrict Ω) ≤ (K : ℝ≥0∞) * (eLpNorm u q (volume.restrict Ω)
          + ∑ k, eLpNorm (g k) q (volume.restrict Ω)) := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨K, hK⟩ := exists_eLpNorm_sobolevConj_le_domain hd hΩopen hΩb hC1 hp hpp'
  exact RungBound.mono_exponent (hp.trans_lt' one_pos) hpq (K := K) hK

end EllipticPdes.Embedding
