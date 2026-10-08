import KLS.MomentRescalingData

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma measurePreserving_symm_of_measurableEquiv
    (e : Space n ≃ᵐ Space n) (he : MeasurePreserving e volume volume) :
    MeasurePreserving e.symm volume volume := by
  refine ⟨e.symm.measurable, ?_⟩
  have hh : (volume.map e).map e.symm = volume := by
    rw [Measure.map_map e.symm.measurable e.measurable]
    have hid : e.symm ∘ e = (id : Space n → Space n) := by funext x; simp
    rw [hid, Measure.map_id]
  rwa [he.map_eq] at hh

lemma map_potentialMeasure_of_volumePreserving
    (e : Space n ≃ᵐ Space n) (he : MeasurePreserving e volume volume)
    {W : Space n → ℝ} (hW : Measurable W) :
    (potentialMeasure W).map e = potentialMeasure (W ∘ e.symm) := by
  unfold potentialMeasure
  rw [map_withDensity_measurableEquiv e volume _ (by fun_prop), he.map_eq]
  rfl

lemma map_restrict_measurableEquiv (e : Space n ≃ᵐ Space n)
    (μ : Measure (Space n)) (K : Set (Space n)) :
    (μ.restrict K).map e = (μ.map e).restrict (e '' K) := by
  have hh := e.restrict_map μ (e '' K)
  rw [e.preimage_image] at hh
  exact hh.symm

/-- A proved volume-preserving coordinate/gradient conjugacy transports the
actual weighted gradient equation, without requiring the source to equal u. -/
theorem weighted_gradient_transport_of_volumePreserving_conjugacy
    (e : Space n ≃ᵐ Space n) (he : MeasurePreserving e volume volume)
    {u v W V : Space n → ℝ} (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (hgradient : gradient v ∘ e.symm = e ∘ gradient u) :
    (potentialMeasure (W ∘ e)).map (gradient v) =
      (potentialMeasure (V ∘ e.symm)).restrict (e '' K) := by
  have hes := measurePreserving_symm_of_measurableEquiv e he
  have hsource : (potentialMeasure W).map e.symm = potentialMeasure (W ∘ e) :=
    map_potentialMeasure_of_volumePreserving e.symm hes hW
  rw [← hsource, Measure.map_map (measurable_gradient v) e.symm.measurable,
    hgradient, ← Measure.map_map e.measurable (measurable_gradient u), hpush,
    map_restrict_measurableEquiv, map_potentialMeasure_of_volumePreserving e he hV]

end KLS
end
