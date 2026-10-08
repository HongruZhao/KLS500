import KLS.QuadraticFenchelBounds
import KLS.MomentAlexandrovEquation

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma map_withDensity_comp_gradient (ρ : Measure (Space n)) (u : Space n → ℝ)
    {w : Space n → ℝ≥0∞} (hw : Measurable w) :
    (ρ.withDensity (fun x => w (gradient u x))).map (gradient u) =
      (ρ.map (gradient u)).withDensity w := by
  ext S hS
  rw [Measure.map_apply (measurable_gradient _) hS,
    withDensity_apply _ (hS.preimage (measurable_gradient _)), withDensity_apply _ hS,
    ← lintegral_indicator hS,
    lintegral_map (hw.indicator hS) (measurable_gradient _),
    ← lintegral_indicator (hS.preimage (measurable_gradient _))]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : gradient u x ∈ S
    · simp only [indicator_of_mem hx, indicator_of_mem (show x ∈ gradient u ⁻¹' S from hx)]
    · simp only [indicator_of_notMem hx,
        indicator_of_notMem (show x ∉ gradient u ⁻¹' S from hx)]

/-- Reweighting the original moment identity gives an exact pushforward of
the actual Monge--Ampere density to Lebesgue measure on the true target. -/
theorem map_gradient_momentMongeAmpereMeasure
    {u V : Space n → ℝ} (hu : Measurable u) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    (momentMongeAmpereMeasure u V).map (gradient u) = volume.restrict K := by
  rw [← potentialMeasure_withDensity_exp_gradient hu hV,
    map_withDensity_comp_gradient _ _ hV.exp.ennreal_ofReal]
  change (MomentMap.gradientPushforward u).withDensity _ = _
  rw [hpush, restrict_potentialMeasure_withDensity_exp hV hK]

/-- The exact real-valued transport identity retains the genuine target
restriction and the genuine source density. -/
theorem integral_comp_gradient_mul_real_moment_density
    {u V ψ : Space n → ℝ} (hu : Measurable u) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : Measurable ψ) :
    (∫ x, Real.exp (-u x + V (gradient u x)) * ψ (gradient u x)) = ∫ p in K, ψ p := by
  have hm := map_gradient_momentMongeAmpereMeasure hu hV hK hpush
  rw [← hm, integral_map_of_stronglyMeasurable (measurable_gradient _) hψ.stronglyMeasurable]
  rw [momentMongeAmpereMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_momentMongeAmpereDensity hu hV)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [momentMongeAmpereDensity, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

lemma closedBall_subset_target_of_quadratic_closeness
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ) :
    closedBall p₀ (R / 4) ⊆ K := by
  intro p hp
  obtain ⟨x, hx, hpx⟩ := exists_interior_contact_of_quadratic_closeness hLip.continuous hc hR hδ hclose hp
  have hh := subgradientImage_subset_closure_of_weak_momentMap hLip hc hK.measurableSet hKc hpush
    (interior (closedBall x₀ R)) ⟨x, hx, hpx⟩
  exact hK.closure_eq ▸ hh

lemma tsupport_comp_gradient_subset_closedBall
    {u ψ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall p₀ (R / 4)) :
    tsupport (ψ ∘ gradient u) ⊆ closedBall x₀ R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  apply interior_subset
  apply mem_interior_closedBall_of_central_subgradient hu.continuous hc hR hδ hclose
  · exact hψs (subset_closure hx)
  · exact gradient_mem_convexSubgradient hc.convexOn (hu.differentiable (by norm_num) x)

/-- Localized compact tests have genuinely integrable source integrands;
compactness of their pulled-back support is proved from quadratic closeness. -/
theorem integrable_comp_gradient_mul_real_moment_density_of_quadratic_closeness
    {u V ψ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hV : Continuous V) (hψ : Continuous ψ)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall p₀ (R / 4)) :
    Integrable (fun x => Real.exp (-u x + V (gradient u x)) * ψ (gradient u x)) := by
  have hg : Continuous (gradient u) := continuous_gradient_of_contDiff hu
  have hs : HasCompactSupport (ψ ∘ gradient u) :=
    (isCompact_closedBall x₀ R).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_gradient_subset_closedBall hu hc hR hδ hclose hψs)
  exact ((Real.continuous_exp.comp (hu.continuous.neg.add (hV.comp hg))).mul (hψ.comp hg)).integrable_of_hasCompactSupport
    hs.mul_left

/-- An inner dual compact test can be integrated against full Lebesgue
measure, and its transported source expression is integrable and localized. -/
theorem localized_moment_transport_of_quadratic_closeness
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : Continuous ψ)
    {x₀ p₀ : Space n} {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall x₀ R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ p₀ c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall p₀ (R / 4)) :
    Integrable (fun x => Real.exp (-u x + V (gradient u x)) * ψ (gradient u x)) ∧
      (∫ x, Real.exp (-u x + V (gradient u x)) * ψ (gradient u x)) = ∫ p, ψ p := by
  refine ⟨integrable_comp_gradient_mul_real_moment_density_of_quadratic_closeness
    (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush)
    (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush)
    hV hψ hR hδ hclose hψs, ?_⟩
  rw [integral_comp_gradient_mul_real_moment_density hLip.continuous.measurable hV.measurable
    hK.measurableSet hpush hψ.measurable]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  apply image_eq_zero_of_notMem_tsupport
  exact fun hps => hp ((closedBall_subset_target_of_quadratic_closeness hLip hc hK hKc hpush
    hR hδ hclose) (hψs hps))

end KLS
end
