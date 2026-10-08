import KLS.LogConcavityMoments

/-! One genuine radial exponential moment for the full compact-set
log-concave probability class, obtained from the proved geometric tail. -/
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
noncomputable section
namespace KLS

set_option maxHeartbeats 400000

private theorem iUnion_exponential_norm_shells {n : ℕ} {R : ℝ} (hR : 0 < R) :
    (⋃ k : ℕ, {x : Space n | (2 * (k : ℝ) + 1) * R < ‖x‖ ∧
      ‖x‖ ≤ (2 * (k : ℝ) + 3) * R}) = {x | R < ‖x‖} := by
  have hmin : ∀ k : ℕ, (2 * (0 : ℝ) + 1) * R ≤ (2 * (k : ℝ) + 1) * R := by
    intro k
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hnb : ¬ BddAbove (range (fun k : ℕ => (2 * (k : ℝ) + 1) * R)) := by
    rw [not_bddAbove_iff]
    intro M
    obtain ⟨k, hk⟩ := exists_nat_gt (M / R)
    refine ⟨(2 * (k : ℝ) + 1) * R, mem_range_self k, ?_⟩
    have := (div_lt_iff₀ hR).mp hk
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h := iUnion_Ioc_map_succ_eq_Ioi (by simpa using hmin) hnb
  have hpre := congrArg (fun s : Set ℝ => (fun x : Space n => ‖x‖) ⁻¹' s) h
  ext x
  have hx := Set.ext_iff.mp hpre x
  simpa only [mem_preimage, mem_iUnion, mem_Ioc, mem_Ioi, mem_ofPred_eq,
    Nat.bot_eq_zero, Order.succ_eq_add_one, Nat.cast_add,
    Nat.cast_one, Nat.cast_zero, mul_add, mul_one, add_assoc, zero_mul, mul_zero,
    zero_add, one_mul, show (1 : ℝ) + 2 = 3 by norm_num, add_comm (2 : ℝ) 1] using hx

theorem integrable_exp_norm_of_geometric_tail {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {R q b : ℝ} (hR : 0 < R) (hq0 : 0 ≤ q) (hb : 0 ≤ b)
    (hqb : q * Real.exp (2 * b * R) < 1)
    (htail : ∀ k : ℕ, μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤ q ^ k) :
    Integrable (fun x : Space n => Real.exp (b * ‖x‖)) μ := by
  let s : ℕ → Set (Space n) := fun k =>
    {x | (2 * (k : ℝ) + 1) * R < ‖x‖ ∧ ‖x‖ ≤ (2 * (k : ℝ) + 3) * R}
  have hc : Continuous (fun x : Space n => Real.exp (b * ‖x‖)) := by fun_prop
  have hint : ∀ k : ℕ, IntegrableOn (fun x : Space n => Real.exp (b * ‖x‖)) (s k) μ := by
    intro k
    apply (hc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space n) ((2 * (k : ℝ) + 3) * R))).mono_set
    intro x hx
    simpa using hx.2
  have hqnorm : ‖(q * Real.exp (2 * b * R) : ℝ)‖ < 1 := by
    rwa [Real.norm_of_nonneg (mul_nonneg hq0 (Real.exp_nonneg _))]
  have hsumm0 : Summable (fun k : ℕ => (q * Real.exp (2 * b * R)) ^ k) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hsumm : Summable (fun k : ℕ => Real.exp (3 * b * R) *
      (q * Real.exp (2 * b * R)) ^ k) := hsumm0.mul_left _
  have hsummInt : Summable (fun k : ℕ => ∫ x in s k, ‖Real.exp (b * ‖x‖)‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => ?_) hsumm
    calc
      ∫ x in s k, ‖Real.exp (b * ‖x‖)‖ ∂μ ≤
          ‖∫ x in s k, ‖Real.exp (b * ‖x‖)‖ ∂μ‖ := le_abs_self _
      _ ≤ Real.exp (b * ((2 * (k : ℝ) + 3) * R)) * μ.real (s k) := by
        apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _)
        intro x hx
        simp only [Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hb)
      _ ≤ Real.exp (b * ((2 * (k : ℝ) + 3) * R)) * q ^ k := by
        exact mul_le_mul_of_nonneg_left
          ((measureReal_mono (fun x hx => hx.1)).trans (htail k)) (Real.exp_nonneg _)
      _ = Real.exp (3 * b * R) * (q * Real.exp (2 * b * R)) ^ k := by
        rw [show b * ((2 * (k : ℝ) + 3) * R) = 3 * b * R + (k : ℝ) * (2 * b * R) by ring,
          Real.exp_add, Real.exp_nat_mul, mul_pow]
        ring
  have hout := integrableOn_iUnion_of_summable_integral_norm hint hsummInt
  have hin := hc.continuousOn.integrableOn_compact (μ := μ)
    (isCompact_closedBall (0 : Space n) R)
  have hall := hin.union hout
  have hcover : closedBall (0 : Space n) R ∪ ⋃ k, s k = univ := by
    rw [show (⋃ k, s k) = {x | R < ‖x‖} from iUnion_exponential_norm_shells hR]
    ext x
    simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt ‖x‖ R
  simpa only [hcover, integrableOn_univ] using hall

theorem measureLogConcave.exists_pos_integrable_exp_norm {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    ∃ b : ℝ, 0 < b ∧ Integrable (fun x : Space n => Real.exp (b * ‖x‖)) μ := by
  obtain ⟨R, q, hR, hq0, hq1, ht⟩ := hμ.exists_geometric_norm_tail
  have hz : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun k : ℕ => q * Real.exp (2 * (1 / ((k : ℝ) + 1)) * R))
      atTop (𝓝 q) := by
    have ht : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) * R) atTop (𝓝 0) := by
      simpa using (hz.const_mul 2).mul_const R
    simpa using ((Real.continuous_exp.tendsto 0).comp ht).const_mul q
  obtain ⟨k, hk⟩ := ((tendsto_order.1 he).2 1 hq1).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  exact integrable_exp_norm_of_geometric_tail hR hq0 (by positivity) hk ht

end KLS
end
