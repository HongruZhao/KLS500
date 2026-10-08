import KLS.CovarianceCumulantPDE

/-! A finite family of actual linear scores gives the adaptive covariance
cancellation, before inserting a particular covariance square root. -/
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem thirdCumulant_const_mul_add_score (hμ : IsCompact μ.support)
    {q f g h k : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) (c : ℝ) :
    tiltThirdCumulant μ q f g (fun x => c * h x + k x) =
      c * tiltThirdCumulant μ q f g h + tiltThirdCumulant μ q f g k := by
  have hi (a : Space n → ℝ) (ha : Continuous a) : Integrable a (μ.tilted q) :=
    integrable_tilted_of_compact_support hμ hq
      (integrable_of_continuous_compact_support_measure hμ ha)
  have hm : tiltAverage μ q (fun x => c * h x + k x) =
      c * tiltAverage μ q h + tiltAverage μ q k := by
    unfold tiltAverage
    rw [integral_add ((hi h hh).const_mul c) (hi k hk), integral_const_mul]
  unfold tiltThirdCumulant
  rw [hm]
  change (∫ x, (f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) *
    (c * h x + k x - (c * tiltAverage μ q h + tiltAverage μ q k)) ∂μ.tilted q) = _
  have he : (fun x => (f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) *
      (c * h x + k x - (c * tiltAverage μ q h + tiltAverage μ q k))) =
    (fun x => c * ((f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) *
      (h x - tiltAverage μ q h)) +
      (f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) * (k x - tiltAverage μ q k)) := by
    funext x
    ring
  rw [he, integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)), integral_const_mul]
  rfl

theorem cumulant_centered_quadratic_identity (hμ : IsCompact μ.support)
    {q f g h : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    tiltThirdCumulant μ q f g (fun x => tiltAverage μ q h * h x + (-(h x)^2 / 2)) +
      1 / 2 * tiltFourthCumulant μ q f g h h =
        -ProbabilityTheory.covariance f h (μ.tilted q) *
          ProbabilityTheory.covariance g h (μ.tilted q) := by
  rw [thirdCumulant_const_mul_add_score hμ hq hf hg hh (by fun_prop)]
  have h := KLS.StandardLocalization.cumulant_quadratic_score_identity hμ hq hf hg hh
  linarith

theorem cumulant_score_family_identity {ι : Type*} [Fintype ι]
    (hμ : IsCompact μ.support) {q f g : Space n → ℝ}
    (hq : Continuous q) (hf : Continuous f) (hg : Continuous g)
    {h : ι → Space n → ℝ} (hh : ∀ k, Continuous (h k)) :
    tiltThirdCumulant μ q f g
        (fun x => ∑ k, (tiltAverage μ q (h k) * h k x + (-(h k x)^2 / 2))) +
      1 / 2 * ∑ k, tiltFourthCumulant μ q f g (h k) (h k) =
        -(∑ k, ProbabilityTheory.covariance f (h k) (μ.tilted q) *
          ProbabilityTheory.covariance g (h k) (μ.tilted q)) := by
  rw [KLS.StandardLocalization.tiltThirdCumulant_sum_score hμ hq hf hg
    (fun k => by fun_prop), Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [neg_mul] using cumulant_centered_quadratic_identity hμ hq hf hg (hh k)

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulant_score_family_identity
