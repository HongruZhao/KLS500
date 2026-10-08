/-
Licensed compatibility excerpt from BrownianMotion.Auxiliary.StoppedProcess,
RemyDegenne/brownian-motion at 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9.
Released under Apache 2.0; see BROWNIAN_LICENSE.
-/
module
public import Mathlib.Probability.Process.Stopping
@[expose] public section
namespace MeasureTheory
variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} [Nonempty ι] [LinearOrder ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X : ι → Ω → E}
@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]
end MeasureTheory
