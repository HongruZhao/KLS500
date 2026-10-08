import KLS.IsotropicGeometricTail

/-! Quantitative polynomial moments from the fixed arithmetic-shell bound.
The constants depend only on the moment order, not on the measure. -/
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual disjoint arithmetic norm shells. -/
def normArithmeticShell (R : ℝ) (k : ℕ) : Set (Space n) :=
  {x | (2 * (k : ℝ) + 1) * R < ‖x‖ ∧ ‖x‖ ≤ (2 * (k : ℝ) + 3) * R}

lemma measurableSet_normArithmeticShell (R : ℝ) (k : ℕ) :
    MeasurableSet (normArithmeticShell (n := n) R k) := by
  unfold normArithmeticShell
  measurability

lemma iUnion_normArithmeticShell {R : ℝ} (hR : 0 < R) :
    (⋃ k : ℕ, normArithmeticShell (n := n) R k) = {x | R < ‖x‖} := by
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
  simpa only [normArithmeticShell, mem_preimage, mem_iUnion, mem_Ioc, mem_Ioi,
    mem_ofPred_eq, Nat.bot_eq_zero, Order.succ_eq_add_one, Nat.cast_add,
    Nat.cast_one, Nat.cast_zero, mul_add, mul_one, add_assoc, zero_mul, mul_zero,
    zero_add, one_mul, show (1 : ℝ) + 2 = 3 by norm_num, add_comm (2 : ℝ) 1] using hx

lemma pairwise_disjoint_normArithmeticShell {R : ℝ} (hR : 0 < R) :
    ∀ k l : ℕ, k ≠ l → Disjoint (normArithmeticShell (n := n) R k)
      (normArithmeticShell R l) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hxk hxl
  change (2 * (k : ℝ) + 1) * R < ‖x‖ ∧ ‖x‖ ≤ (2 * (k : ℝ) + 3) * R at hxk
  change (2 * (l : ℝ) + 1) * R < ‖x‖ ∧ ‖x‖ ≤ (2 * (l : ℝ) + 3) * R at hxl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hh : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
    nlinarith
  · have hh : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
    nlinarith

lemma summable_arithmetic_geometric_moment (p : ℕ) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 3) ^ p * (1 / 3 : ℝ) ^ k) := by
  have hq : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have hsum : Summable (fun k : ℕ => (5 : ℝ) ^ p *
      ((k : ℝ) ^ p * (1 / 3 : ℝ) ^ k + (1 / 3 : ℝ) ^ k)) :=
    ((summable_pow_mul_geometric_of_norm_lt_one p hq).add
      (summable_geometric_of_norm_lt_one hq)).mul_left ((5 : ℝ) ^ p)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hsum
  intro k
  have hbound : (2 * (k : ℝ) + 3) ^ p ≤ (5 : ℝ) ^ p * ((k : ℝ) ^ p + 1) := by
    by_cases hk : k = 0
    · subst k
      have hh : (3 : ℝ) ^ p ≤ (5 : ℝ) ^ p := by gcongr; norm_num
      have hn : 0 ≤ (5 : ℝ) ^ p * (0 : ℝ) ^ p := by positivity
      simpa only [Nat.cast_zero, mul_zero, zero_add] using
        (hh.trans (by nlinarith : (5 : ℝ) ^ p ≤ (5 : ℝ) ^ p * ((0 : ℝ) ^ p + 1)))
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      calc
        (2 * (k : ℝ) + 3) ^ p ≤ (5 * (k : ℝ)) ^ p := by
          apply pow_le_pow_left₀ (by positivity)
          linarith
        _ = (5 : ℝ) ^ p * (k : ℝ) ^ p := mul_pow _ _ _
        _ ≤ (5 : ℝ) ^ p * ((k : ℝ) ^ p + 1) := by gcongr; linarith
  have hm := mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ (1 / 3 : ℝ) ^ k)
  nlinarith [hm]

/-- A finite, order-only constant, specified by an actually summable series. -/
def geometricNormMomentConstant (p : ℕ) : ℝ :=
  1 + ∑' k : ℕ, (2 * (k : ℝ) + 3) ^ p * (1 / 3 : ℝ) ^ k

lemma geometricNormMomentConstant_pos (p : ℕ) : 0 < geometricNormMomentConstant p := by
  unfold geometricNormMomentConstant
  have h : 0 ≤ ∑' k : ℕ, (2 * (k : ℝ) + 3) ^ p * (1 / 3 : ℝ) ^ k :=
    tsum_nonneg fun _ => by positivity
  linarith

/-- An actual moment estimate follows from the fixed shell tail and genuine
integrability; the latter is supplied for the full log-concave class below. -/
theorem integral_norm_pow_le_geometric_constant {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {R : ℝ} (hR : 0 < R)
    (htail : ∀ k : ℕ, μ.real {x | (2 * (k : ℝ) + 1) * R < ‖x‖} ≤ (1 / 3 : ℝ) ^ k)
    (p : ℕ) (hp : Integrable (fun x : Space n => ‖x‖ ^ p) μ) :
    (∫ x, ‖x‖ ^ p ∂μ) ≤ R ^ p * geometricNormMomentConstant p := by
  have hins : (∫ x in closedBall (0 : Space n) R, ‖x‖ ^ p ∂μ) ≤ R ^ p := by
    calc
      _ ≤ ‖∫ x in closedBall (0 : Space n) R, ‖x‖ ^ p ∂μ‖ := le_abs_self _
      _ ≤ R ^ p * μ.real (closedBall (0 : Space n) R) := by
        apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _)
        intro x hx
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p)]
        apply pow_le_pow_left₀ (norm_nonneg x)
        simpa using hx
      _ ≤ R ^ p := by
        have hmass : μ.real (closedBall (0 : Space n) R) ≤ 1 :=
          (measureReal_mono (subset_univ _)).trans_eq probReal_univ
        exact mul_le_of_le_one_right (pow_nonneg hR.le p) hmass
  have hsh (k : ℕ) : (∫ x in normArithmeticShell R k, ‖x‖ ^ p ∂μ) ≤
      R ^ p * ((2 * (k : ℝ) + 3) ^ p * (1 / 3 : ℝ) ^ k) := by
    calc
      _ ≤ ‖∫ x in normArithmeticShell R k, ‖x‖ ^ p ∂μ‖ := le_abs_self _
      _ ≤ ((2 * (k : ℝ) + 3) * R) ^ p * μ.real (normArithmeticShell R k) := by
        apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _)
        intro x hx
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) p)]
        exact pow_le_pow_left₀ (norm_nonneg x) hx.2 p
      _ ≤ ((2 * (k : ℝ) + 3) * R) ^ p * (1 / 3 : ℝ) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (measureReal_mono (fun x hx => hx.1)).trans (htail k)
      _ = _ := by rw [mul_pow]; ring
  have hhas := hasSum_integral_iUnion (fun k => measurableSet_normArithmeticShell R k)
    (pairwise_disjoint_normArithmeticShell hR) hp.restrict
  have hout : (∫ x in {x : Space n | R < ‖x‖}, ‖x‖ ^ p ∂μ) ≤
      R ^ p * ∑' k : ℕ, (2 * (k : ℝ) + 3) ^ p * (1 / 3 : ℝ) ^ k := by
    rw [← iUnion_normArithmeticShell hR, hhas.tsum_eq.symm,
      ← tsum_mul_left]
    exact hhas.summable.tsum_le_tsum hsh
      ((summable_arithmetic_geometric_moment p).mul_left (R ^ p))
  have hc : (closedBall (0 : Space n) R)ᶜ = {x | R < ‖x‖} := by ext x; simp
  rw [← integral_add_compl measurableSet_closedBall hp, hc]
  unfold geometricNormMomentConstant
  nlinarith [hins, hout]

/-- Uniform dimension-dependent moments for every actual isotropic compact-set
log-concave probability, without density or spectral assumptions. -/
theorem measureLogConcave.isotropic_integral_norm_pow_le {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (hiso : IsIsotropic μ) (p : ℕ) :
    (∫ x, ‖x‖ ^ p ∂μ) ≤
      (isotropicTailRadius n) ^ p * geometricNormMomentConstant p := by
  apply integral_norm_pow_le_geometric_constant (isotropicTailRadius_pos n) _ p
    (hμ.integrable_norm_pow p)
  intro k
  apply (hμ.isotropic_norm_tail_le hiso k).trans
  exact mul_le_of_le_one_left (by positivity) (by norm_num)

end KLS
end
#print axioms KLS.integral_norm_pow_le_geometric_constant
#print axioms KLS.measureLogConcave.isotropic_integral_norm_pow_le
