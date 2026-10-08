import KLS.CovarianceDerivativeCumulants

/-! The exact deterministic cumulant cancellation behind standard localization. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization
open LevyStochCalc
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- Exact per-coordinate cancellation, under the actual normalized tilted law. -/
theorem cumulant_quadratic_score_identity (hμ : IsCompact μ.support)
    {q f g h : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    tiltThirdCumulant μ q f g (fun x => -(h x) ^ 2 / 2) +
      tiltAverage μ q h * tiltThirdCumulant μ q f g h +
      1 / 2 * tiltFourthCumulant μ q f g h h =
        -ProbabilityTheory.covariance f h (μ.tilted q) *
          ProbabilityTheory.covariance g h (μ.tilted q) := by
  letI := tilted_isProbability_of_compact_support hμ hq
  have havg (a : Space n → ℝ) :
      tiltAverage μ q (fun x => a x * (-(h x) ^ 2 / 2)) =
        -(tiltAverage μ q (fun x => a x * (h x) ^ 2)) / 2 := by
    unfold tiltAverage
    have he : (fun x => a x * (-(h x) ^ 2 / 2)) = fun x => -(a x * (h x) ^ 2) / 2 := by
      funext x
      ring
    rw [he, integral_div, integral_neg]
  have havg0 : tiltAverage μ q (fun x => -(h x) ^ 2 / 2) =
      -(tiltAverage μ q (fun x => (h x) ^ 2)) / 2 := by
    simpa only [one_mul] using havg (fun _ => 1)
  rw [tiltThirdCumulant_eq hμ hq hf hg (by fun_prop),
    tiltThirdCumulant_eq hμ hq hf hg hh,
    tiltFourthCumulant_eq hμ hq hf hg hh hh,
    ProbabilityTheory.covariance_eq_sub (memLp_two_continuous_tilted hμ hq hf)
      (memLp_two_continuous_tilted hμ hq hh),
    ProbabilityTheory.covariance_eq_sub (memLp_two_continuous_tilted hμ hq hg)
      (memLp_two_continuous_tilted hμ hq hh)]
  simp_rw [havg, havg0, pow_two, mul_assoc]
  change _ = - (tiltAverage μ q (fun x => f x * h x) - tiltAverage μ q f * tiltAverage μ q h) *
    (tiltAverage μ q (fun x => g x * h x) - tiltAverage μ q g * tiltAverage μ q h)
  ring

/-- Linearity of the actual centered third moment in its score. -/
theorem tiltThirdCumulant_sum_score {ι : Type*} [Fintype ι]
    (hμ : IsCompact μ.support) {q f g : Space n → ℝ}
    (hq : Continuous q) (hf : Continuous f) (hg : Continuous g)
    {h : ι → Space n → ℝ} (hh : ∀ k, Continuous (h k)) :
    tiltThirdCumulant μ q f g (fun x => ∑ k, h k x) =
      ∑ k, tiltThirdCumulant μ q f g (h k) := by
  have hi (a : Space n → ℝ) (ha : Continuous a) : Integrable a (μ.tilted q) :=
    integrable_tilted_of_compact_support hμ hq
      (integrable_of_continuous_compact_support_measure hμ ha)
  have hm : tiltAverage μ q (fun x => ∑ k, h k x) = ∑ k, tiltAverage μ q (h k) := by
    exact integral_finsetSum Finset.univ (fun k _ => hi (h k) (hh k))
  unfold tiltThirdCumulant
  rw [hm]
  change (∫ x, (f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) *
      ((∑ k, h k x) - ∑ k, tiltAverage μ q (h k)) ∂μ.tilted q) = _
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact integral_finsetSum Finset.univ (fun k _ => hi _ (by fun_prop))

theorem quadratic_time_cumulant_eq_sum (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) (i j : Fin n) :
    tiltThirdCumulant μ q (fun x => x i) (fun x => x j) (fun x => -‖x‖ ^ 2 / 2) =
      ∑ k : Fin n, tiltThirdCumulant μ q (fun x => x i) (fun x => x j)
        (fun x => -(x k) ^ 2 / 2) := by
  have he : (fun x : Space n => -‖x‖ ^ 2 / 2) =
      fun x => ∑ k : Fin n, -(x k) ^ 2 / 2 := by
    funext x
    simp only [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [he]
  exact tiltThirdCumulant_sum_score hμ hq (by fun_prop) (by fun_prop) (fun _ => by fun_prop)

/-- The actual time-state covariance observable satisfies the localization
backward equation, with matrix product A² and the actual tilted mean. -/
theorem covariance_generator_eq_neg_square (hμ : IsCompact μ.support)
    (i j : Fin n) (z : Fin (n + 1) → ℝ) :
    coordDeriv (covarianceGradient μ i j) 0 z +
      (∑ k : Fin n, mean μ (z 0) (Fin.tail z) k *
        coordDeriv (covarianceGradient μ i j) k.succ z) +
      1 / 2 * ∑ k : Fin n, coordDeriv₂ (covarianceHessian μ i j) k.succ k.succ z =
        -((covariance μ (z 0) (Fin.tail z)) * (covariance μ (z 0) (Fin.tail z))) i j := by
  rw [covariance_time_derivative hμ, quadratic_time_cumulant_eq_sum hμ
    (continuous_exponent_state (z 0) (Fin.tail z))]
  simp_rw [covariance_space_derivative hμ, covariance_space_second_derivative hμ]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have h := cumulant_quadratic_score_identity hμ
    (continuous_exponent_state (z 0) (Fin.tail z))
    (f := fun x => x i) (g := fun x => x j) (h := fun x => x k)
    (by fun_prop) (by fun_prop) (by fun_prop)
  have hs : covariance μ (z 0) (Fin.tail z) j k = covariance μ (z 0) (Fin.tail z) k j :=
    ProbabilityTheory.covariance_comm (fun x : Space n => x j) (fun x => x k)
  change _ = -(covariance μ (z 0) (Fin.tail z) i k * covariance μ (z 0) (Fin.tail z) k j)
  rw [← hs]
  convert h using 1 <;> simp only [mean, law, tiltAverage, covariance, neg_mul]

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.cumulant_quadratic_score_identity

#print axioms KLS.StandardLocalization.covariance_generator_eq_neg_square
