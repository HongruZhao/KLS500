/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.SobolevLadder
public import EllipticPdes.Embedding.ClassicalDeriv

/-!
# Smoothness of a family closed under differentiation

Put the two halves together. The Sobolev ladder raises every member of a family closed under weak
differentiation from `L²` to `L^{2d}` on an inner ball, Morrey turns that into a Hölder
representative, and the representatives inherit the weak gradients of the members they represent.
A continuous function with a continuous weak gradient is classically differentiable, so each
representative is differentiable with its derivative again in the family, and an induction on the
order reads that as `C^∞`.

Only one ball is lost, at the Morrey step. The ladder shrinks internally between the two radii
it is given, and the differentiability argument runs on the inner ball itself, since the
derivative of a representative is a representative. Were the derivative to force a further
shrinking, no fixed ball would serve every order.

## Main declarations

* `EllipticPdes.Embedding.contDiffOn_of_gradClosed`: smooth representatives for a family closed
  under weak differentiation.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Classical derivatives of continuous representatives of a family.** Let `v i` represent
`F i` on the open set `B`, let `F i` have its weak gradient in the family, and let `Good n i` say
that `n` more orders are available at `i`, so that the derivative of a member that has `n + 1`
has `n`. If every `v i` with `Good n i` is continuous, then each `v i` with `Good (n + 1) i` is
differentiable on `B` with the next members as its partial derivatives, and each `v i` with
`Good n i` is `C^n`. -/
theorem contDiffOn_of_ae_eq_family {B : Set (EuclideanSpace ℝ (Fin d))} (hBo : IsOpen B)
    {ι : Type*} {F v : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    (Good : ℕ → ι → Prop) (hstep : ∀ n i k, Good (n + 1) i → Good n (nxt i k))
    (hae : ∀ n i, Good n i → v i =ᵐ[volume.restrict B] F i)
    (hint : ∀ n i, Good n i → IntegrableOn (F i) B volume)
    (hgrad : ∀ n i, Good (n + 1) i → HasWeakGradOn B (F i) (fun k => F (nxt i k)))
    (hcont : ∀ n i, Good n i → ContinuousOn (v i) B) :
    (∀ n i, Good (n + 1) i → ∀ y ∈ B, HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) ∧
      ∀ n i, Good n i → ContDiffOn ℝ (n : ℕ) (v i) B := by
  have hfd : ∀ n i, Good (n + 1) i →
      ∀ y ∈ B, HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y := fun n i hi y hy =>
    hasFDerivAt_of_continuousOn_hasWeakGradOn hBo.measurableSet hBo
      ((hint _ i hi).congr (hae _ i hi).symm)
      (fun k => (hint n _ (hstep n i k hi)).congr (hae n _ (hstep n i k hi)).symm)
      (hcont _ i hi) (fun k => hcont n _ (hstep n i k hi))
      ((hgrad n i hi).congr_ae (hae _ i hi).symm fun k => (hae n _ (hstep n i k hi)).symm) hy
  refine ⟨hfd, fun n => ?_⟩
  induction n with
  | zero => exact fun i hi => by simpa using hcont 0 i hi
  | succ n ih =>
    intro i hi
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
      contDiffOn_succ_iff_fderiv_of_isOpen hBo]
    refine ⟨fun y hy => ((hfd n i hi y hy).differentiableAt).differentiableWithinAt, by simp, ?_⟩
    have hsum : ContDiffOn ℝ (n : ℕ) (fun y => gradCLM (fun k => v (nxt i k)) y) B := by
      change ContDiffOn ℝ (n : ℕ) (fun y => ∑ k, v (nxt i k) y •
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) B
      exact ContDiffOn.sum fun k _ => (ih (nxt i k) (hstep n i k hi)).smul contDiffOn_const
    exact hsum.congr fun y hy => (hfd n i hi y hy).fderiv

/-- **Smooth representatives of a family closed under weak differentiation.** Let `F` assign a
function to each index, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`,
and let every member lie in `L²` there. Then on any smaller concentric ball every member has a
representative smooth to every order.

The representatives are produced together, one per index, because the derivative of the
representative of `F i` has to be the representative of `F (nxt i k)` rather than some other
function agreeing with it almost everywhere. Continuity is what makes the choice rigid: two
continuous representatives of one class on an open ball are equal. -/
theorem contDiffOn_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {nxt : ι → Fin d → ι}
    (hgrad : ∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) :
    ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (v i) (Metric.ball c r)) ∧
        ∀ i, v i =ᵐ[volume.restrict (Metric.ball c r)] F i := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp : (d : ℝ) < 2 * (d : ℝ) := by linarith
  have hFint : ∀ i, IntegrableOn (F i) (Metric.ball c r) volume := fun i =>
    ((hmem i).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable (by norm_num)
  -- The ladder lifts every member to `L^{2d}`, and Morrey gives each a Hölder representative.
  obtain ⟨C, hC⟩ := morrey_ball hd hp c hr
  choose v hvae hvhol using fun i => hC (F i) (fun k => F (nxt i k)) (hFint i)
    (fun k => by
      rw [ofReal_two_mul_natCast]
      exact memLp_two_mul_of_gradClosed hd c hr hrR hgrad hmem (nxt i k))
    ((hgrad i).mono (Metric.ball_subset_ball hrR.le))
  have hγ : 0 < morreyExponent d (2 * (d : ℝ)) :=
    Real.toNNReal_pos.mpr (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp))
  obtain ⟨-, hcn⟩ := contDiffOn_of_ae_eq_family (F := F) (v := v) Metric.isOpen_ball
    (fun _ _ => True) (fun _ _ _ _ => trivial) (fun _ i _ => hvae i) (fun _ i _ => hFint i)
    (fun _ i _ => (hgrad i).mono (Metric.ball_subset_ball hrR.le))
    (fun _ i _ => (hvhol i).continuousOn hγ)
  exact ⟨v, fun i => contDiffOn_infty.mpr fun n => hcn n i trivial, hvae⟩

end EllipticPdes.Embedding
