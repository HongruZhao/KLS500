import KLS.TruncatedConjugateAgreement
import KLS.ContactSetLocalSingleton

/-! Positive finite Alexandrov bounds on a single positive sublevel of the
centered truncation rule out multiple original supporting slopes. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem convexSubgradient_subsingleton_of_truncated_volume_bounds
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x : Space n} {M R : ℝ} (hx : ‖x‖ < M) (hR : 0 < R)
    {a b : ℝ≥0∞} (ha : 0 < a) (hatop : a < ∞) (hb : 0 < b) (hbtop : b < ∞)
    (hbounds : ∀ S : Set (Space n), IsSigmaCompact S →
      S ⊆ {p | centeredTruncatedConjugate u x M p ≤ R} →
        a * volume S ≤ volume (convexSubgradientImage (centeredTruncatedConjugate u x M) S) ∧
        volume (convexSubgradientImage (centeredTruncatedConjugate u x M) S) ≤ b * volume S) :
    (convexSubgradient u x).Subsingleton := by
  let f := centeredTruncatedConjugate u x M
  have hM : 0 ≤ M := (norm_nonneg x).trans hx.le
  have hf : Continuous f := continuous_centeredTruncatedConjugate hu x hM
  have hfc : ConvexOn ℝ univ f := convexOn_centeredTruncatedConjugate hu x hM
  have hnonneg : ∀ p, 0 ≤ f p := centeredTruncatedConjugate_nonneg hu hx.le
  let : IsFiniteMeasure (potentialMeasure f) :=
    isFiniteMeasure_potentialMeasure_centeredTruncatedConjugate hu hx
  obtain ⟨p, hp⟩ := convexSubgradient_nonempty hu hc x
  have hfp : f p = 0 := (centeredTruncatedConjugate_eq_zero_iff hu hc hx).mpr hp
  have hp0 : (0 : Space n) ∈ convexSubgradient f p := by
    intro q
    simpa only [hfp, inner_zero_left, add_zero] using hnonneg q
  have hsingle := supportContactSet_sublevel_subsingleton_of_sigmaCompact_bounds
    hf hfc ha hatop hb hbtop hbounds hp0 (hfp ▸ hR)
  have hmem : ∀ q ∈ convexSubgradient u x,
      q ∈ supportContactSet f p 0 ∩ {q | f q ≤ R} := by
    intro q hq
    have hfq : f q = 0 := (centeredTruncatedConjugate_eq_zero_iff hu hc hx).mpr hq
    constructor
    · simp only [supportContactSet, mem_ofPred_eq, hfp, hfq, inner_zero_left, add_zero]
    · change f q ≤ R
      rw [hfq]
      exact hR.le
  intro q hq r hr
  exact hsingle (hmem q hq) (hmem r hr)

end KLS
end

#print axioms KLS.convexSubgradient_subsingleton_of_truncated_volume_bounds
