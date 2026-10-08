/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic

/-!
# Limits in the graph space

A sequence in `H¹(Ω)` converges when its function part and each gradient component converge in
`L²(Ω)`, and convergence in `L²` is convergence of the seminorm of the difference of
representatives. This file states those reductions once.

## Main declarations

* `EllipticPdes.Sobolev.H1amb.mk`: the vector with a given function part and gradient components.
* `EllipticPdes.Sobolev.H1amb.tendsto_iff`: convergence in `H¹` is convergence of the parts.
* `EllipticPdes.Sobolev.H1amb.tendsto_iff_eLpNorm`: the same through representatives.
* `EllipticPdes.Sobolev.tendsto_testGraph_iff`: convergence of test graphs.
* `EllipticPdes.Sobolev.exists_seq_isTestFn_tendsto`: every element of `H₀¹` is a limit of test
  graphs.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Convergence in `L²` of classes with given representatives is convergence of the `L²`
seminorm of the difference of the representatives to the limit class. -/
lemma tendsto_Lp_iff_eLpNorm {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {u : ι → Lp ℝ 2 μ} {a : Lp ℝ 2 μ} {f : ι → α → ℝ} (hf : ∀ n, ⇑(u n) =ᵐ[μ] f n) :
    Tendsto u l (𝓝 a) ↔ Tendsto (fun n => eLpNorm (f n - ⇑a) 2 μ) l (𝓝 0) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).trans
    (tendsto_congr fun n => eLpNorm_congr_ae ((hf n).sub EventuallyEq.rfl))

namespace H1amb

/-- The ambient vector with function part `u` and gradient components `g`. -/
def mk (u : L2D Ω) (g : Fin d → L2D Ω) : H1amb Ω := WithLp.toLp 2 (Fin.cons u g)

/-- The function part of `mk u g` is `u`. -/
@[simp] lemma fn_mk (u : L2D Ω) (g : Fin d → L2D Ω) : (mk u g).fn = u := rfl

/-- The `i`-th gradient component of `mk u g` is `g i`. -/
@[simp] lemma grad_mk (u : L2D Ω) (g : Fin d → L2D Ω) (i : Fin d) : (mk u g).grad i = g i := rfl

/-- Convergence in `H¹` is convergence of the function part and of each gradient component
in `L²`. -/
lemma tendsto_iff {ι : Type*} {l : Filter ι} {U : ι → H1amb Ω} {V : H1amb Ω} :
    Tendsto U l (𝓝 V) ↔
      Tendsto (fun n => (U n).fn) l (𝓝 V.fn) ∧
        ∀ i, Tendsto (fun n => (U n).grad i) l (𝓝 (V.grad i)) := by
  have hcoord : Tendsto U l (𝓝 V) ↔ ∀ j, Tendsto (fun n => U n j) l (𝓝 (V j)) := by
    refine ⟨fun h j => ((continuous_apply j).tendsto _).comp
      (((PiLp.continuous_ofLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto V).comp h), fun h => ?_⟩
    exact ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto V.ofLp).comp
      (tendsto_pi_nhds.mpr h)
  rw [hcoord, Fin.forall_fin_succ]
  rfl

/-- Convergence in `H¹` through representatives: if `f n` represents the function part of `U n`
and `G n i` its `i`-th gradient component, then `U n → V` exactly when the `L²` seminorms of the
differences with the limit components tend to zero. -/
lemma tendsto_iff_eLpNorm {ι : Type*} {l : Filter ι} {U : ι → H1amb Ω} {V : H1amb Ω}
    {f : ι → EuclideanSpace ℝ (Fin d) → ℝ} {G : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ∀ n, ⇑(U n).fn =ᵐ[volume.restrict Ω] f n)
    (hG : ∀ n i, ⇑((U n).grad i) =ᵐ[volume.restrict Ω] G n i) :
    Tendsto U l (𝓝 V) ↔
      Tendsto (fun n => eLpNorm (f n - ⇑V.fn) 2 (volume.restrict Ω)) l (𝓝 0) ∧
        ∀ i, Tendsto (fun n => eLpNorm (G n i - ⇑(V.grad i)) 2 (volume.restrict Ω)) l (𝓝 0) := by
  rw [tendsto_iff, tendsto_Lp_iff_eLpNorm hf]
  exact and_congr_right fun _ => forall_congr' fun i => tendsto_Lp_iff_eLpNorm fun n => hG n i

end H1amb

/-- Convergence of test graphs in `H¹`, through the test functions and their partials. -/
lemma tendsto_testGraph_iff {φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : ∀ n, IsTestFn Ω (φ n)) {V : H1amb Ω} :
    Tendsto (fun n => (h n).testGraph) atTop (𝓝 V) ↔
      Tendsto (fun n => eLpNorm (φ n - ⇑V.fn) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
        ∀ i, Tendsto (fun n => eLpNorm (partialD i (φ n) - ⇑(V.grad i)) 2 (volume.restrict Ω))
          atTop (𝓝 0) :=
  H1amb.tendsto_iff_eLpNorm (fun n => (h n).coeFn_testCls)
    (fun n i => (h n).coeFn_partialCls i)

/-- Every element of `H₀¹(Ω)` is the limit of the graphs of a sequence of test functions. -/
lemma exists_seq_isTestFn_tendsto {V : H1amb Ω} (hV : V ∈ H01 Ω) :
    ∃ (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (h : ∀ n, IsTestFn Ω (φ n)),
      Tendsto (fun n => (h n).testGraph) atTop (𝓝 V) := by
  have hV' : V ∈ closure (testGraphSet Ω) := by rw [← coe_H01]; exact hV
  obtain ⟨X, hX, hXt⟩ := mem_closure_iff_seq_limit.mp hV'
  choose φ hφ hXφ using fun n => (hX n : ∃ φ, ∃ h : IsTestFn Ω φ, X n = h.testGraph)
  exact ⟨φ, hφ, by simpa only [← hXφ] using hXt⟩

/-- The graph of a test function lies in `H₀¹`. -/
lemma IsTestFn.testGraph_mem_H01 {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    h.testGraph ∈ H01 Ω :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, h, rfl⟩)

end EllipticPdes.Sobolev
