import KLS.LogConcavitySupport
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# A canonical density from shrinking balls

The countable lower limit of normalized closed-ball masses is measurable.
For compact-set log-concave measures it satisfies the pointwise log-concavity
inequality, and differentiation of measures identifies it almost everywhere
with the ordinary Radon–Nikodym derivative. No absolute continuity is assumed.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace KLS

/-- A fixed positive sequence decreasing to zero. -/
def densityRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem densityRadius_pos (k : ℕ) : 0 < densityRadius k := by
  unfold densityRadius
  positivity

theorem densityRadius_tendsto : Tendsto densityRadius atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall densityRadius_pos⟩

/-- Normalized closed-ball mass at a fixed scale. -/
def ballDensity {n : ℕ} (μ : Measure (Space n)) (r : ℝ) (x : Space n) : ℝ≥0∞ :=
  μ (closedBall x r) / volume (closedBall (0 : Space n) r)

/-- The lower limit along fixed positive radii, including exceptional points. -/
def lowerBallDensity {n : ℕ} (μ : Measure (Space n)) (x : Space n) : ℝ≥0∞ :=
  liminf (fun k => ballDensity μ (densityRadius k) x) atTop

theorem measurable_ballDensity {n : ℕ} (μ : Measure (Space n)) [SFinite μ] (r : ℝ) :
    Measurable (ballDensity μ r) := by
  have hm : Measurable fun x : Space n => μ (closedBall x r) := by
    have hs : MeasurableSet {p : Space n × Space n | dist p.2 p.1 ≤ r} :=
      isClosed_le (by fun_prop) continuous_const |>.measurableSet
    exact measurable_measure_prodMk_left hs
  exact hm.div_const _

theorem measurable_lowerBallDensity {n : ℕ} (μ : Measure (Space n)) [SFinite μ] :
    Measurable (lowerBallDensity μ) :=
  Measurable.liminf (fun k => measurable_ballDensity μ (densityRadius k))

theorem ballDensity_eq_div_center {n : ℕ} (μ : Measure (Space n)) (r : ℝ) (x : Space n) :
    ballDensity μ r x = μ (closedBall x r) / volume (closedBall x r) := by
  rw [ballDensity, Measure.addHaar_closedBall_center volume x r]

theorem measureLogConcave.ballDensity_logConcave {n : ℕ} {μ : Measure (Space n)}
    (hμ : measureLogConcave μ) {r : ℝ} (hr : 0 < r)
    (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ballDensity μ r x ^ t * ballDensity μ r y ^ (1 - t) ≤
      ballDensity μ r (t • x + (1 - t) • y) := by
  have hvol0 : volume (closedBall (0 : Space n) r) ≠ 0 :=
    (measure_closedBall_pos volume _ hr).ne'
  have hvoltop : volume (closedBall (0 : Space n) r) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  have h : (μ (closedBall x r)) ^ t * (μ (closedBall y r)) ^ (1 - t) ≤
      μ (closedBall (t • x + (1 - t) • y) r) :=
    (hμ _ _ (isCompact_closedBall x r) (isCompact_closedBall y r) t ht0 ht1).trans
      (measure_mono (affineSetCombination_closedBall_subset x y ht0.le ht1.le r))
  unfold ballDensity
  rw [ENNReal.div_rpow_of_nonneg _ _ ht0.le,
    ENNReal.div_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1.le),
    ← ENNReal.mul_div_mul_comm
      (Or.inl (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hvol0) ht0.le).ne')
      (Or.inr (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hvol0)
        (sub_nonneg.mpr ht1.le)).ne'),
    ← ENNReal.rpow_add t (1 - t) hvol0 hvoltop]
  simpa using ENNReal.div_le_div_right h _

private theorem rpow_liminf {u : ℕ → ℝ≥0∞} {t : ℝ} (ht : 0 < t) :
    (liminf u atTop) ^ t = liminf (fun k => u k ^ t) atTop := by
  exact (ENNReal.orderIsoRpow t ht).monotone.map_liminf_of_continuousAt u
    ENNReal.continuous_rpow_const.continuousAt

theorem measureLogConcave.lowerBallDensity_logConcave {n : ℕ} {μ : Measure (Space n)}
    (hμ : measureLogConcave μ) (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    lowerBallDensity μ x ^ t * lowerBallDensity μ y ^ (1 - t) ≤
      lowerBallDensity μ (t • x + (1 - t) • y) := by
  unfold lowerBallDensity
  rw [rpow_liminf ht0, rpow_liminf (sub_pos.mpr ht1)]
  exact ENNReal.le_liminf_mul.trans (liminf_le_liminf (Eventually.of_forall fun k =>
    hμ.ballDensity_logConcave (densityRadius_pos k) x y ht0 ht1))

theorem lowerBallDensity_ae_eq_rnDeriv {n : ℕ} (μ : Measure (Space n))
    [IsLocallyFiniteMeasure μ] :
    lowerBallDensity μ =ᵐ[volume] μ.rnDeriv volume := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume] with x hx
  have h := (hx.comp densityRadius_tendsto).liminf_eq
  simpa only [lowerBallDensity, ballDensity_eq_div_center, Function.comp_def] using h

theorem lowerBallDensity_ae_eq_inv_rnDeriv {n : ℕ} (μ : Measure (Space n))
    [IsLocallyFiniteMeasure μ] :
    lowerBallDensity μ =ᵐ[μ] fun x => (volume.rnDeriv μ x)⁻¹ := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume μ] with x hx
  have h := (hx.comp densityRadius_tendsto).inv.liminf_eq
  have heq (k : ℕ) :
      (volume (closedBall x (densityRadius k)) / μ (closedBall x (densityRadius k)))⁻¹ =
      ballDensity μ (densityRadius k) x := by
    rw [ballDensity_eq_div_center]
    exact ENNReal.inv_div (Or.inr measure_closedBall_lt_top.ne)
      (Or.inr (measure_closedBall_pos volume x (densityRadius_pos k)).ne')
  simpa only [heq, lowerBallDensity, Function.comp_def] using h

theorem lowerBallDensity_pos_ae {n : ℕ} (μ : Measure (Space n))
    [IsLocallyFiniteMeasure μ] : ∀ᵐ x ∂μ, 0 < lowerBallDensity μ x := by
  filter_upwards [lowerBallDensity_ae_eq_inv_rnDeriv μ,
    Measure.rnDeriv_lt_top volume μ] with x hx hfin
  rw [hx]
  exact pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hfin.ne)

theorem lowerBallDensity_lt_top_ae {n : ℕ} (μ : Measure (Space n))
    [IsLocallyFiniteMeasure μ] : ∀ᵐ x ∂volume, lowerBallDensity μ x < ∞ := by
  filter_upwards [lowerBallDensity_ae_eq_rnDeriv μ,
    Measure.rnDeriv_lt_top μ volume] with x hx hfin
  rwa [hx]

end KLS
end

#print axioms KLS.measureLogConcave.lowerBallDensity_logConcave
#print axioms KLS.lowerBallDensity_pos_ae
#print axioms KLS.lowerBallDensity_lt_top_ae
