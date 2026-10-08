import KLS.DefinitionBridges

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace KLS

private theorem rpow_iSup_pos {ι : Sort*} (f : ι → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, (f i) ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup f

/-- The compact-set hypothesis extends to a measurable second input by inner
regularity. The target set need not have a measurable Minkowski sum. -/
theorem measureLogConcave.le_measure_of_compact_measurable_interpolation
    {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hμ : measureLogConcave μ) {E F A : Set (Space n)}
    (hE : IsCompact E) (hF : MeasurableSet F)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsub : affineSetCombination t E F ⊆ A) :
    (μ E) ^ t * (μ F) ^ (1 - t) ≤ μ A := by
  have ht : 0 < 1 - t := by linarith
  conv_lhs => arg 2; arg 1; rw [hF.measure_eq_iSup_isCompact μ]
  simp_rw [rpow_iSup_pos _ ht, ENNReal.mul_iSup]
  refine iSup_le fun K => iSup_le fun hKF => iSup_le fun hK => ?_
  refine (hμ E K hE hK t ht0 ht1).trans (measure_mono ?_)
  rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact hsub ⟨(x, y), ⟨hx, hKF hy⟩, rfl⟩

/-- A ball interpolated with a sufficiently remote norm tail remains outside
the same ball. This geometric fact does not involve a measure. -/
theorem affineSetCombination_ball_tail_subset {n : ℕ} {R S t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hRS : (1 + t) * R ≤ (1 - t) * S) :
    affineSetCombination t (closedBall (0 : Space n) R) {x | S < ‖x‖} ⊆
      {x | R < ‖x‖} := by
  rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hy' : (1 - t) * S < (1 - t) * ‖y‖ :=
    mul_lt_mul_of_pos_left hy (by linarith)
  have heq : (1 - t) • y = (t • x + (1 - t) • y) - t • x := by abel
  have hn := norm_sub_le (t • x + (1 - t) • y) (t • x)
  rw [← heq, norm_smul_of_nonneg (by linarith : 0 ≤ 1 - t),
    norm_smul_of_nonneg ht0] at hn
  have hxmul := mul_le_mul_of_nonneg_left hx' ht0
  change R < ‖t • x + (1 - t) • y‖
  linarith

/-- The exact compact-set log-concavity predicate gives a tail interpolation
inequality without density or absolute-continuity assumptions. -/
theorem measureLogConcave.norm_tail_interpolation {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : measureLogConcave μ)
    {R S t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hRS : (1 + t) * R ≤ (1 - t) * S) :
    (μ (closedBall (0 : Space n) R)) ^ t *
      (μ {x | S < ‖x‖}) ^ (1 - t) ≤ μ {x | R < ‖x‖} := by
  apply hμ.le_measure_of_compact_measurable_interpolation
    (isCompact_closedBall 0 R) (measurableSet_lt measurable_const continuous_norm.measurable)
    ht0 ht1
  exact affineSetCombination_ball_tail_subset ht0.le ht1 hRS

/-- The tail estimate on equally spaced shells, before division. -/
theorem measureLogConcave.norm_tail_mul_pow_le {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : measureLogConcave μ)
    (R : ℝ) (k : ℕ) :
    (μ (closedBall (0 : Space n) R)) ^ k *
      μ {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤
        (μ {x | R < ‖x‖}) ^ (k + 1) := by
  rcases eq_or_lt_of_le (Nat.zero_le k) with hk | hk
  · subst k
    simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have ht0 : 0 < (k : ℝ) / ((k : ℝ) + 1) := div_pos hk0 hkp
  have ht1 : (k : ℝ) / ((k : ℝ) + 1) < 1 := (div_lt_one hkp).2 (by linarith)
  have heq : (1 + (k : ℝ) / ((k : ℝ) + 1)) * R =
      (1 - (k : ℝ) / ((k : ℝ) + 1)) * ((2 * (k : ℝ) + 1) * R) := by
    field_simp
    ring
  have h := ENNReal.rpow_le_rpow (hμ.norm_tail_interpolation ht0 ht1 heq.le) hkp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hkp.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  have h1 : (k : ℝ) / ((k : ℝ) + 1) * ((k : ℝ) + 1) = k := by field_simp
  have h2 : (1 - (k : ℝ) / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = 1 := by
    field_simp
    ring
  rw [h1, h2, ENNReal.rpow_one] at h
  simpa only [← Nat.cast_add_one, ENNReal.rpow_natCast] using h

/-- Every shell has a geometric bound determined by the probability mass
inside and outside one ball. -/
theorem measureLogConcave.norm_tail_toReal_le_geometric {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : measureLogConcave μ)
    (R : ℝ) (hp : 0 < μ.real (closedBall (0 : Space n) R)) (k : ℕ) :
    μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤
      μ.real {x | R < ‖x‖} *
        (μ.real {x | R < ‖x‖} / μ.real (closedBall (0 : Space n) R)) ^ k := by
  have h := ENNReal.toReal_mono
    (ENNReal.pow_ne_top (measure_ne_top μ _))
    (hμ.norm_tail_mul_pow_le R k)
  have h' : μ.real (closedBall (0 : Space n) R) ^ k *
      μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤
        (μ.real {x | R < ‖x‖}) ^ (k + 1) := by
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow] using h
  calc
    μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤
        (μ.real {x | R < ‖x‖}) ^ (k + 1) /
          (μ.real (closedBall (0 : Space n) R)) ^ k :=
      (le_div_iff₀ (pow_pos hp k)).mpr (by nlinarith [h'])
    _ = _ := by rw [div_pow, pow_succ]; ring

/-- Any finite-dimensional probability measure has a positive radius whose
ball contains more than half the mass. -/
theorem exists_pos_radius_half_lt_ball {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] :
    ∃ R : ℝ, 0 < R ∧ (1 / 2 : ℝ) < μ.real (closedBall (0 : Space n) R) := by
  obtain ⟨K, _, hK, hmass⟩ := (MeasurableSet.univ : MeasurableSet (univ : Set (Space n))).exists_lt_isCompact
    (μ := μ) (r := (1 / 2 : ℝ≥0∞)) (by simp)
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space n)
  refine ⟨R, hR, ?_⟩
  have hball := hmass.trans_le (measure_mono hsub)
  have hr := (ENNReal.toReal_lt_toReal (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)
    (measure_ne_top μ _)).mpr hball
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    Measure.real] using hr

/-- Therefore compact-set log-concave probabilities have an exponentially
small bound along an arithmetic sequence of norm shells. -/
theorem measureLogConcave.exists_geometric_norm_tail {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    ∃ R q : ℝ, 0 < R ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ k : ℕ, μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤ q ^ k := by
  obtain ⟨R, hR, hp⟩ := exists_pos_radius_half_lt_ball μ
  let p := μ.real (closedBall (0 : Space n) R)
  let a := μ.real {x | R < ‖x‖}
  have hp0 : 0 < p := by dsimp [p]; linarith
  have ha : a = 1 - p := by
    have hcomp : {x : Space n | R < ‖x‖} = (closedBall 0 R)ᶜ := by ext x; simp
    dsimp [a, p]
    rw [hcomp, measureReal_compl measurableSet_closedBall, probReal_univ]
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hap : a < p := by dsimp [p] at *; linarith
  have ha1 : a ≤ 1 := by linarith
  refine ⟨R, a / p, hR, div_nonneg ha0 hp0.le, (div_lt_one hp0).mpr hap, ?_⟩
  intro k
  exact (hμ.norm_tail_toReal_le_geometric R hp0 k).trans
    (mul_le_of_le_one_left (pow_nonneg (div_nonneg ha0 hp0.le) k) ha1)

end KLS

#print axioms KLS.measureLogConcave.le_measure_of_compact_measurable_interpolation

#print axioms KLS.measureLogConcave.norm_tail_interpolation
#print axioms KLS.measureLogConcave.norm_tail_mul_pow_le

#print axioms KLS.measureLogConcave.exists_geometric_norm_tail
