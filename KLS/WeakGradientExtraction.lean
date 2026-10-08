/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license; see sources/licenses/EllipticPDE-Apache-2.0.txt.
Authors: Alejandro Soto Franco

The generic Hilbert-space subsequence lemma is selectively adapted from
EllipticPDE revision 2138a84891e025a4e0ad3013f5b1041fac8dce5e,
lean/EllipticPdes/Regularity/DiffQuotientBound.lean, lines 493–526.
The wrapper, namespace, and concrete derivative extraction below are local.
-/
import KLS.ForcedCaccioppoli
import KLS.MollificationApproximation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Weak limits and extraction of actual weak coordinate derivatives -/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology ENNReal RealInnerProductSpace
noncomputable section
namespace KLS

/-- Bounded sequences in a separable real Hilbert space have weakly convergent
subsequences, with the bound retained by the actual limit. -/
theorem exists_weak_limit_of_bounded_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {x : ℕ → E} {M : ℝ} (hx : ∀ m, ‖x m‖ ≤ M) :
    ∃ (g' : E) (σ : ℕ → ℕ), StrictMono σ ∧ ‖g'‖ ≤ M ∧
      ∀ y : E, Filter.Tendsto (fun m => ⟪x (σ m), y⟫) Filter.atTop (nhds ⟪g', y⟫) := by
  set F : ℕ → WeakDual ℝ E :=
    fun m => WeakDual.toStrongDual.symm (InnerProductSpace.toDual ℝ E (x m)) with hFdef
  have hFtoS : ∀ m, WeakDual.toStrongDual (F m) = InnerProductSpace.toDual ℝ E (x m) :=
    fun m => WeakDual.toStrongDual.apply_symm_apply _
  have hFmem : ∀ m, F m ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℝ E) M := by
    intro m
    simp only [Set.mem_preimage, hFtoS m, Metric.mem_closedBall, dist_zero_right]
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hx m
  obtain ⟨L, hLmem, σ, hσmono, hLtend⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E 0 M hFmem
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), σ, hσmono, ?_, ?_⟩
  · rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hLmem
  · intro y
    have heval := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hLtend) y
    have hL1 : ∀ m, topDualPairing ℝ E (F (σ m)) y = ⟪x (σ m), y⟫ := by
      intro m
      change (F (σ m)) y = ⟪x (σ m), y⟫
      rw [show (F (σ m)) y = (InnerProductSpace.toDual ℝ E (x (σ m))) y from rfl,
        InnerProductSpace.toDual_apply_apply]
    have hL2 : topDualPairing ℝ E L y
        = ⟪(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), y⟫ := by
      change L y = ⟪(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), y⟫
      rw [InnerProductSpace.toDual_symm_apply]
      exact (WeakDual.toStrongDual_apply L y).symm
    rw [hL2] at heval
    exact heval.congr (fun m => hL1 m)



/-- Strong convergence of scalar representatives gives convergence of their
actual L² equivalence classes. -/
lemma tendsto_toLp_of_eLpNorm_sub_tendsto_zero {n : ℕ}
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hu : MemLp u 2 volume)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hu.toLp u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (k : ℕ) : ‖(hf k).toLp (f k) - hu.toLp u‖ =
      (eLpNorm (f k - u) 2 volume).toReal := by
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
  simp_rw [hnorm]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hconv

/-- Compact C¹ approximants converging strongly in L² and with uniformly
bounded coordinate-gradient energy yield an actual L² weak derivative.
The limit identity holds for every compact C¹ test; no regularity of the
limiting scalar function is assumed. -/
theorem exists_weak_coordinateDerivative_of_approximation {n : ℕ}
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hc : ∀ k, HasCompactSupport (f k))
    (hu : MemLp u 2 volume)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 volume) atTop (𝓝 0))
    (i : Fin n) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ k, (∫ x, coordinateDerivative (f k) i x ^ 2) ≤ M) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)), ‖g‖ ≤ Real.sqrt M ∧
      ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, u x * coordinateDerivative ψ i x) = -(∫ x, g x * ψ x) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hfLp (k : ℕ) : MemLp (f k) 2 volume :=
    (hf k).continuous.memLp_of_hasCompactSupport (hc k)
  have hdLp (k : ℕ) : MemLp (coordinateDerivative (f k) i) 2 volume :=
    (contDiff_coordinateDerivative (hf k) (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative (hc k) i)
  let F (k : ℕ) : Lp ℝ 2 volume := (hfLp k).toLp (f k)
  let D (k : ℕ) : Lp ℝ 2 volume := (hdLp k).toLp (coordinateDerivative (f k) i)
  let U : Lp ℝ 2 volume := hu.toLp u
  have hn (k : ℕ) : ‖D k‖ ^ 2 = ∫ x, coordinateDerivative (f k) i x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hdLp k).coeFn_toLp] with x hx
    simp only [D, hx, RCLike.inner_apply, conj_trivial, pow_two]
  have hb (k : ℕ) : ‖D k‖ ≤ Real.sqrt M := by
    apply (Real.le_sqrt (norm_nonneg _) hM).mpr
    rw [hn]
    exact hbound k
  obtain ⟨g, σ, hσ, hgnorm, hweak⟩ := exists_weak_limit_of_bounded_hilbert hb
  refine ⟨g, hgnorm, ?_⟩
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψLp : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  let P : Lp ℝ 2 volume := hψLp.toLp ψ
  let DP : Lp ℝ 2 volume := hdψLp.toLp (coordinateDerivative ψ i)
  have hinnerD (k : ℕ) : inner ℝ (D k) P =
      ∫ x, coordinateDerivative (f k) i x * ψ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hdLp k).coeFn_toLp, hψLp.coeFn_toLp] with x hx hy
    simp [D, P, hx, hy, RCLike.inner_apply, mul_comm]
  have hinnerF (k : ℕ) : inner ℝ (F k) DP =
      ∫ x, f k x * coordinateDerivative ψ i x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hfLp k).coeFn_toLp, hdψLp.coeFn_toLp] with x hx hy
    simp [F, DP, hx, hy, RCLike.inner_apply, mul_comm]
  have hinnerU : inner ℝ U DP = ∫ x, u x * coordinateDerivative ψ i x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hdψLp.coeFn_toLp] with x hx hy
    simp [U, DP, hx, hy, RCLike.inner_apply, mul_comm]
  have hinnerg : inner ℝ g P = ∫ x, g x * ψ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψLp.coeFn_toLp] with x hx
    simp [P, hx, RCLike.inner_apply, mul_comm]
  have hid (k : ℕ) : inner ℝ (D k) P = -inner ℝ (F k) DP := by
    rw [hinnerD, hinnerF]
    have he := integral_mul_coordinateDerivative_of_hasCompactSupport_left (hf k) hψ (hc k) i
    linarith
  have hstrong : Tendsto F atTop (𝓝 U) :=
    tendsto_toLp_of_eLpNorm_sub_tendsto_zero hfLp hu hconv
  have hlim : Tendsto (fun k => -inner ℝ (F (σ k)) DP) atTop (𝓝 (-inner ℝ U DP)) :=
    ((hstrong.comp hσ.tendsto_atTop).inner (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => DP) atTop (𝓝 DP))).neg
  have heq : inner ℝ g P = -inner ℝ U DP :=
    tendsto_nhds_unique (hweak P) (hlim.congr (fun k => (hid (σ k)).symm))
  rw [hinnerg, hinnerU] at heq
  linarith

end KLS
end

#print axioms KLS.exists_weak_limit_of_bounded_hilbert
#print axioms KLS.tendsto_toLp_of_eLpNorm_sub_tendsto_zero
#print axioms KLS.exists_weak_coordinateDerivative_of_approximation
