import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Compactness.Lindelof

/-!
# Local Rademacher infrastructure

The theorems in this file establish almost-everywhere differentiability of every
locally Lipschitz test function and transfer it to absolutely continuous measures.
They do not assume or prove a Poincaré inequality or the KLS conjecture.

The norm identity also identifies the existing mathlib gradient with the operator
norm of the Fréchet derivative. Both total definitions are zero at points where
there is no derivative; the Rademacher theorem shows that those points are null
for the absolutely continuous measures under consideration.
-/

open Filter MeasureTheory Measure Set
open scoped Topology

namespace KLS

section Rademacher

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {μ ν : Measure E}

/-- Local Rademacher theorem for an arbitrary additive Haar measure.

The countable neighborhood cover is essential: an uncountable union of the
exceptional null sets would not justify this conclusion. -/
theorem locallyLipschitz_ae_differentiableAt [IsAddHaarMeasure μ]
    (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  classical
  choose K U hU hLip using hf
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds_interior hU
  have hlocal : ∀ z ∈ s,
      ∀ᵐ x ∂μ, x ∈ interior (U z) → DifferentiableAt ℝ f x := by
    intro z _
    filter_upwards [(hLip z).ae_differentiableWithinAt_of_mem (μ := μ)] with x hx
    intro hxin
    exact (hx (interior_subset hxin)).differentiableAt
      (mem_interior_iff_mem_nhds.mp hxin)
  filter_upwards [(ae_ball_iff hs).mpr hlocal] with x hx
  have hmem : x ∈ ⋃ z ∈ s, interior (U z) := by
    rw [hcover]
    exact mem_univ x
  rcases mem_iUnion₂.mp hmem with ⟨z, hzs, hxz⟩
  exact hx z hzs hxz

/-- Rademacher's conclusion passes to any measure absolutely continuous with
respect to additive Haar measure. No density smoothness is required. -/
theorem locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
    [IsAddHaarMeasure ν] (hμ : μ ≪ ν) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
  hμ.ae_le (locallyLipschitz_ae_differentiableAt (μ := ν) hf)

end Rademacher

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The Hilbert gradient and the Fréchet derivative have the same norm, including
at points where the total derivative definitions take their default value. -/
theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simpa only [gradient] using
    (InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ f x)

/-- The total gradient is measurable, so its norm can be used in a nonnegative
extended integral without replacing divergent integrals by a real default value. -/
theorem measurable_gradient [MeasurableSpace E] [BorelSpace E] (f : E → ℝ) :
    Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

/-- Almost everywhere, the total gradient is an actual gradient when the test
function is locally Lipschitz and the measure is absolutely continuous. -/
theorem locallyLipschitz_ae_hasGradientAt
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsAddHaarMeasure ν]
    (hμ : μ ≪ ν) {f : E → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂μ, HasGradientAt f (gradient f x) x := by
  filter_upwards
    [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hμ hf] with x hx
  exact hx.hasGradientAt

end Gradient

end KLS

#print axioms KLS.locallyLipschitz_ae_differentiableAt
#print axioms KLS.locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous
#print axioms KLS.norm_gradient_eq_norm_fderiv
#print axioms KLS.measurable_gradient
#print axioms KLS.locallyLipschitz_ae_hasGradientAt
