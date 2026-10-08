import KLS.WeightedMomentMeasure

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem weighted_closedBall_subset_target_of_quadratic_closeness
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hW : Measurable W)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ) :
    closedBall p₀ (R / 4) ⊆ K := by
  intro p hp
  obtain ⟨x, _, hpx⟩ := exists_interior_contact_of_quadratic_closeness
    hLip.continuous hc hR hδ hclose hp
  exact weighted_convexSubgradient_subset_target hLip hc hW hK hKc hpush x hpx

theorem integral_comp_gradient_mul_weighted_density
    {u W V ψ : Space n → ℝ} (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (hψ : Measurable ψ) :
    (∫ x, Real.exp (-W x + V (gradient u x)) * ψ (gradient u x)) = ∫ p in K, ψ p := by
  have hm := map_gradient_weightedMomentMeasure hW hV hK hpush
  rw [← hm, integral_map_of_stronglyMeasurable (measurable_gradient _) hψ.stronglyMeasurable]
  rw [weightedMomentMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_weightedMomentDensity hW hV)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [weightedMomentDensity, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

lemma integrable_comp_gradient_mul_weighted_density_of_quadratic_closeness
    {u W V ψ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V) (hψ : Continuous ψ)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall p₀ (R / 4)) :
    Integrable (fun x => Real.exp (-W x + V (gradient u x)) * ψ (gradient u x)) := by
  have hg : Continuous (gradient u) := continuous_gradient_of_contDiff hu
  have hs : HasCompactSupport (ψ ∘ gradient u) :=
    (isCompact_closedBall x₀ R).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_gradient_subset_closedBall hu hc hR hδ hclose hψs)
  exact ((Real.continuous_exp.comp (hW.neg.add (hV.comp hg))).mul (hψ.comp hg)).integrable_of_hasCompactSupport
    hs.mul_left

/-- The localized exact transport identity requires only the genuine weighted
pushforward and the C1 strictly convex potential. No equality W = u is used. -/
theorem localized_weighted_transport_of_quadratic_closeness
    {u W V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (hψ : Continuous ψ)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall p₀ (R / 4)) :
    Integrable (fun x => Real.exp (-W x + V (gradient u x)) * ψ (gradient u x)) ∧
      (∫ x, Real.exp (-W x + V (gradient u x)) * ψ (gradient u x)) = ∫ p, ψ p := by
  refine ⟨integrable_comp_gradient_mul_weighted_density_of_quadratic_closeness
    hu hc hW hV hψ hR hδ hclose hψs, ?_⟩
  rw [integral_comp_gradient_mul_weighted_density hW.measurable hV.measurable
    hK.measurableSet hpush hψ.measurable]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  apply image_eq_zero_of_notMem_tsupport
  exact fun hps => hp ((weighted_closedBall_subset_target_of_quadratic_closeness
    hLip hc.convexOn hW.measurable hK hKc hpush hR hδ hclose) (hψs hps))

end KLS
end
