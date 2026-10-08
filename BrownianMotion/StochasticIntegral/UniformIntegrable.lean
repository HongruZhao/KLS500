/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.Jensen
public import BrownianMotion.Auxiliary.StoppedProcess
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Martingale.OptionalSampling

/-!
Minimal compatibility slice: exactly the three completed upstream helper statements
used by Quasimartingale.CadlagModification. Unrelated unfinished upstream declarations
are deliberately omitted; this file does not claim to port the full upstream module.
-/
public section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology
namespace MeasureTheory
variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma UniformIntegrable.add [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X + Y) p μ := by
  refine ⟨hX.1.add hY.1 hp, ?_⟩
  obtain ⟨CX, hCX⟩ := hX.2
  obtain ⟨CY, hCY⟩ := hY.2
  exact ⟨CX + CY, fun i => (eLpNorm_add_le hp).trans (add_le_add (hCX i) (hCY i))⟩

lemma uniformIntegrable_of_dominated [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : ι → Ω → E} {Y : κ → Ω → F} {p : ℝ≥0∞}
    (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := by
  choose j hj using hX
  refine ⟨unifIntegrable_iff.2 ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.1 hY.1 ε hε
    refine ⟨δ, hδ, fun i s hs => ?_⟩
    exact (eLpNorm_mono_ae (mX i).restrict
      ((hj i).filter_mono ae_restrict_le)).trans (hbound (j i) s hs)
  · obtain ⟨C, hC⟩ := hY.2
    exact ⟨C, fun i => (eLpNorm_mono_ae (mX i) (hj i)).trans (hC (j i))⟩

lemma UniformIntegrable.norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hY : UniformIntegrable X p μ) :
    UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine uniformIntegrable_of_dominated hY ?_ (fun i ↦ ⟨i, by simp⟩)
  exact fun i ↦ (UniformIntegrable.aestronglyMeasurable hY i).norm

end MeasureTheory
