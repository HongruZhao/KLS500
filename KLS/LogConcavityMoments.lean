import KLS.LogConcavityTails

/-!
# Polynomial moments from compact-set log-concavity

The proof uses the geometric norm-tail bound and integrates over bounded
annuli. It does not assume a density, absolute continuity, or isotropy.
-/

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace KLS

/-- The arithmetic annuli used to sum polynomial moments cover exactly the
exterior of the initial ball. -/
private theorem iUnion_norm_shells {n : ℕ} {R : ℝ} (hR : 0 < R) :
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


/-- A geometric bound on arithmetic norm shells gives every nonnegative
integer moment. This general measure-theoretic lemma needs no log-concavity. -/
theorem integrable_norm_pow_of_geometric_tail {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {R q : ℝ} (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htail : ∀ k : ℕ, μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤ q ^ k)
    (p : ℕ) : Integrable (fun x : Space n => ‖x‖ ^ p) μ := by
  let s : ℕ → Set (Space n) := fun k =>
    {x | (2 * (k : ℝ) + 1) * R < ‖x‖ ∧ ‖x‖ ≤ (2 * (k : ℝ) + 3) * R}
  have hc : Continuous (fun x : Space n => ‖x‖ ^ p) := continuous_norm.pow p
  have hint : ∀ k : ℕ, IntegrableOn (fun x : Space n => ‖x‖ ^ p) (s k) μ := by
    intro k
    apply (hc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space n) ((2 * (k : ℝ) + 3) * R))).mono_set
    intro x hx
    simpa using hx.2
  have hqnorm : ‖q‖ < 1 := by rwa [Real.norm_of_nonneg hq0]
  have hsumm : Summable (fun k : ℕ => (5 * R) ^ p *
      ((k : ℝ) ^ p * q ^ k + q ^ k)) :=
    ((summable_pow_mul_geometric_of_norm_lt_one p hqnorm).add
      (summable_geometric_of_norm_lt_one hqnorm)).mul_left ((5 * R) ^ p)
  have hbound : ∀ k : ℕ, ((2 * (k : ℝ) + 3) * R) ^ p ≤
      (5 * R) ^ p * ((k : ℝ) ^ p + 1) := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hpow : (3 * R) ^ p ≤ (5 * R) ^ p := by gcongr; linarith
      have hnon : 0 ≤ (5 * R) ^ p * (0 : ℝ) ^ p := by positivity
      simpa using (hpow.trans (by nlinarith : (5 * R) ^ p ≤
        (5 * R) ^ p * ((0 : ℝ) ^ p + 1)))
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      calc
        ((2 * (k : ℝ) + 3) * R) ^ p ≤ ((5 * R) * k) ^ p := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith
        _ = (5 * R) ^ p * (k : ℝ) ^ p := mul_pow _ _ _
        _ ≤ (5 * R) ^ p * ((k : ℝ) ^ p + 1) := by gcongr; linarith
  have hsummInt : Summable (fun k : ℕ => ∫ x in s k, ‖‖x‖ ^ p‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => ?_) hsumm
    calc
      ∫ x in s k, ‖‖x‖ ^ p‖ ∂μ ≤ ‖∫ x in s k, ‖‖x‖ ^ p‖ ∂μ‖ := le_abs_self _
      _ ≤ ((2 * (k : ℝ) + 3) * R) ^ p * μ.real (s k) := by
        apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _)
        intro x hx
        simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p)]
        exact pow_le_pow_left₀ (norm_nonneg x) hx.2 p
      _ ≤ ((2 * (k : ℝ) + 3) * R) ^ p * q ^ k := by
        gcongr
        exact (measureReal_mono (fun x hx => hx.1)).trans (htail k)
      _ ≤ (5 * R) ^ p * ((k : ℝ) ^ p * q ^ k + q ^ k) := by
        have hh := mul_le_mul_of_nonneg_right (hbound k) (pow_nonneg hq0 k)
        nlinarith [hh]
  have hout := integrableOn_iUnion_of_summable_integral_norm hint hsummInt
  have hin := hc.continuousOn.integrableOn_compact (μ := μ)
    (isCompact_closedBall (0 : Space n) R)
  have hall := hin.union hout
  have hcover : closedBall (0 : Space n) R ∪ ⋃ k, s k = univ := by
    rw [show (⋃ k, s k) = {x | R < ‖x‖} from iUnion_norm_shells hR]
    ext x
    simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt ‖x‖ R
  simpa only [hcover, integrableOn_univ] using hall

/-- All polynomial norm moments exist for the exact compact-set class of
log-concave probability measures. -/
theorem measureLogConcave.integrable_norm_pow {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (p : ℕ) :
    Integrable (fun x : Space n => ‖x‖ ^ p) μ := by
  obtain ⟨R, q, hR, hq0, hq1, ht⟩ := hμ.exists_geometric_norm_tail
  exact integrable_norm_pow_of_geometric_tail hR hq0 hq1 ht p

/-- Polynomial norm functions are square-integrable; this establishes the
integrability needed before using real-valued quadratic variances. -/
theorem measureLogConcave.memLp_two_norm_pow {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (p : ℕ) :
    MemLp (fun x : Space n => ‖x‖ ^ p) 2 μ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using hμ.integrable_norm_pow (p * 2)

/-- All quadratic coordinate monomials belong to L² in the full compact-set
log-concave probability class. -/
theorem measureLogConcave.memLp_two_coordinate_mul {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (i j : Fin n) :
    MemLp (fun x : Space n => x i * x j) 2 μ := by
  apply (hμ.memLp_two_norm_pow 2).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
      (norm_nonneg _) (norm_nonneg _)

end KLS

#print axioms KLS.integrable_norm_pow_of_geometric_tail
#print axioms KLS.measureLogConcave.integrable_norm_pow

#print axioms KLS.measureLogConcave.memLp_two_coordinate_mul
