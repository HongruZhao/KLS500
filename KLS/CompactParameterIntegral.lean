import KLS.RadialTailProfile
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Differentiation of an actual compactly supported parameter integral.
The bound is extracted from a compact product and all domination hypotheses
are proved; no interchange of differentiation and integration is assumed. -/
theorem hasDerivAt_integral_of_local_common_compact_support
    {F D : ℝ → Space n → ℝ} {t r : ℝ} (hr : 0 < r)
    {K : Set (Space n)} (hK : IsCompact K)
    (hF : ∀ s, Continuous (F s)) (hD : ∀ s, Continuous (D s))
    (hDc : ContinuousOn (fun p : ℝ × Space n => D p.1 p.2) (Icc (t-r) (t+r) ×ˢ K))
    (hFs : ∀ s ∈ Ioo (t-r) (t+r), Function.support (F s) ⊆ K)
    (hDs : Function.support (D t) ⊆ K)
    (hderiv : ∀ x, ∀ s ∈ Ioo (t-r) (t+r), HasDerivAt (fun q => F q x) (D s x) s) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, D t x) t := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hDc
  have hFi (s : ℝ) : Integrable (F s) (volume.restrict K) :=
    ContinuousOn.integrableOn_compact hK (hF s).continuousOn
  have hDi : Integrable (D t) (volume.restrict K) :=
    ContinuousOn.integrableOn_compact hK (hD t).continuousOn
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := F) (F' := D)
    (s := Ioo (t-r) (t+r)) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hFi s).aestronglyMeasurable)
    (hFi t) hDi.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      intro s hs
      exact hC (s,x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩)
    (integrable_const C)
    (Eventually.of_forall fun x s hs => hderiv x s hs)).2
  have heD : (∫ x in K, D t x) = ∫ x, D t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      Function.notMem_support.mp (fun hxs => hx (hDs hxs)))
  rw [heD] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by linarith : t-r < t) (by linarith : t < t+r)] with s hs
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact Function.notMem_support.mp (fun hxs => hx (hFs s hs hxs))

end KLS
end
