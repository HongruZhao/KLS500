import KLS.LocalizedMomentTransport
import KLS.MomentAlexandrovOpen

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def weightedMomentDensity (u W V : Space n → ℝ) (x : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-W x + V (gradient u x)))

def weightedMomentMeasure (u W V : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (weightedMomentDensity u W V)

lemma measurable_weightedMomentDensity {u W V : Space n → ℝ}
    (hW : Measurable W) (hV : Measurable V) : Measurable (weightedMomentDensity u W V) :=
  (hW.neg.add (hV.comp (measurable_gradient u))).exp.ennreal_ofReal

lemma weighted_potentialMeasure_withDensity_exp_gradient {u W V : Space n → ℝ}
    (hW : Measurable W) (hV : Measurable V) :
    (potentialMeasure W).withDensity (fun x => ENNReal.ofReal (Real.exp (V (gradient u x)))) =
      weightedMomentMeasure u W V := by
  rw [potentialMeasure, ← withDensity_mul volume
    (f := fun x => ENNReal.ofReal (Real.exp (-W x)))
    (g := fun x => ENNReal.ofReal (Real.exp (V (gradient u x))))
    hW.neg.exp.ennreal_ofReal ((hV.comp (measurable_gradient u)).exp.ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.mul_apply, weightedMomentDensity,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

/-- All supporting slopes lie in the genuine closed convex target, even
when the source weight is independent of the transported convex potential. -/
theorem weighted_convexSubgradient_subset_target
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hW : Measurable W)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (x : Space n) : convexSubgradient u x ⊆ K := by
  have hsource : ∀ᵐ z ∂potentialMeasure W, gradient u z ∈ K := by
    apply ae_of_ae_map (measurable_gradient u).aemeasurable
    rw [hpush]
    exact ae_restrict_mem hK.measurableSet
  exact convexSubgradient_subset_of_ae_gradient_mem hLip hc hK hKc
    ((volume_absolutelyContinuous_potentialMeasure_of_measurable hW).ae_le hsource) x

theorem map_gradient_weightedMomentMeasure
    {u W V : Space n → ℝ} (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K) :
    (weightedMomentMeasure u W V).map (gradient u) = volume.restrict K := by
  rw [← weighted_potentialMeasure_withDensity_exp_gradient hW hV,
    map_withDensity_comp_gradient _ _ hV.exp.ennreal_ofReal,
    hpush, restrict_potentialMeasure_withDensity_exp hV hK]

/-- The actual weighted weak transport gives the ordinary Alexandrov
equation on every sigma-compact set; the source is exp(-W). -/
theorem weightedMomentMeasure_eq_subgradientImage_volume
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsSigmaCompact S) :
    weightedMomentMeasure u W V S = volume (convexSubgradientImage u S) := by
  have hSm := measurableSet_of_isSigmaCompact_space hS
  have hA := measurableSet_of_isSigmaCompact_space (isSigmaCompact_convexSubgradientImage hLip hS)
  have hρ : potentialMeasure W ≪ volume := withDensity_absolutelyContinuous _ _
  have htarget : (potentialMeasure W).map (gradient u) ≪ volume := by
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hAsub : convexSubgradientImage u S ⊆ K := by
    rintro p ⟨x, _, hx⟩
    exact weighted_convexSubgradient_subset_target hLip hc hW hK hKc hpush x hx
  have hh := setLIntegral_comp_gradient_eq_subgradientImage_of_measurable
    hLip hc hρ htarget hSm hA hV.exp.ennreal_ofReal
  rw [hpush] at hh
  rw [← weighted_potentialMeasure_withDensity_exp_gradient hW hV,
    withDensity_apply _ hSm, hh, ← withDensity_apply _ hA,
    restrict_potentialMeasure_withDensity_exp hV hK.measurableSet,
    Measure.restrict_apply hA, inter_eq_self_of_subset_left hAsub]

theorem weighted_moment_alexandrov_equation
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsOpen S) :
    volume (convexSubgradientImage u S) =
      ∫⁻ x in S, ENNReal.ofReal (Real.exp (-W x + V (gradient u x))) := by
  rw [← weightedMomentMeasure_eq_subgradientImage_volume hLip hc hW hV hK hKc hpush
    (isSigmaCompact_of_isOpen_space hS), weightedMomentMeasure, withDensity_apply _ hS.measurableSet]
  rfl

end KLS
end
