import KLS.LocalSectionDeficitComparison

/-! A quantitative dyadic modulus for actual supporting slopes, obtained by
iterating opposite support-deficit comparison. The geometric decay factor is
constructed explicitly and is strictly below one. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem supportDeficit_dyadic_le_on_convex_set
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {S : Set (Space n)} (hSc : Convex ℝ S) {C : ℝ} (hC : 0 < C)
    (hcompare : ∀ x ∈ S, ∀ y ∈ S, ∀ p ∈ convexSubgradient u x,
      ∀ q ∈ convexSubgradient u y, supportDeficit u x p y ≤ C * supportDeficit u y q x)
    {x p v : Space n} (hx : x ∈ S) (hv : x + v ∈ S) (hp : p ∈ convexSubgradient u x) :
    ∀ k : ℕ, supportDeficit u x p (dyadicSectionPoint x v k) ≤
      sectionDeficitContractionFactor C ^ k * supportDeficit u x p (x + v) := by
  apply supportDeficit_dyadic_le hC
  intro k
  have hpoint : dyadicSectionPoint x v (k + 1) ∈ S := by
    have hmem := hSc.add_smul_sub_mem hx hv
      (show (1 / 2 : ℝ) ^ (k + 1) ∈ Icc 0 1 from
        ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩)
    simpa only [dyadicSectionPoint, add_sub_cancel_left] using hmem
  obtain ⟨q, hq⟩ := convexSubgradient_nonempty hu hc (dyadicSectionPoint x v (k + 1))
  exact ⟨q, hq, hcompare x hx _ hpoint p hp q hq⟩

theorem supportDeficit_le_at_dyadic_distance
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    {S : Set (Space n)} (hSc : Convex ℝ S) {C : ℝ} (hC : 0 < C)
    (hcompare : ∀ x ∈ S, ∀ y ∈ S, ∀ p ∈ convexSubgradient u x,
      ∀ q ∈ convexSubgradient u y, supportDeficit u x p y ≤ C * supportDeficit u y q x)
    {x p z : Space n} {r : ℝ} (hr : 0 ≤ r) (hball : closedBall x r ⊆ S)
    (hp : p ∈ convexSubgradient u x) (k : ℕ)
    (hz : ‖z - x‖ ≤ r * (1 / 2 : ℝ) ^ k) :
    supportDeficit u x p z ≤ 2 * (L : ℝ) * r * sectionDeficitContractionFactor C ^ k := by
  let v : Space n := (2 : ℝ) ^ k • (z - x)
  have hpow : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hvnorm : ‖v‖ ≤ r := by
    rw [show ‖v‖ = (2 : ℝ) ^ k * ‖z - x‖ from by
      simp only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]]
    calc
      _ ≤ (2 : ℝ) ^ k * (r * (1 / 2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = r := by nlinarith [congrArg (fun a : ℝ => r * a) hpow]
  have hv : x + v ∈ S := hball (by simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hvnorm)
  have hx : x ∈ S := hball (mem_closedBall_self hr)
  have hpoint : dyadicSectionPoint x v k = z := by
    dsimp [dyadicSectionPoint, v]
    rw [smul_smul, mul_comm ((1 / 2 : ℝ) ^ k), hpow, one_smul]
    abel
  have hh := supportDeficit_dyadic_le_on_convex_set hLip.continuous hc hSc hC hcompare hx hv hp k
  rw [hpoint] at hh
  have hbase := supportDeficit_le_of_lipschitz hLip hp (x + v)
  rw [add_sub_cancel_left] at hbase
  have hbase' : supportDeficit u x p (x + v) ≤ 2 * (L : ℝ) * r :=
    hbase.trans (mul_le_mul_of_nonneg_left hvnorm (by positivity))
  have hκ := (sectionDeficitContractionFactor_pos_lt_half hC).1
  calc
    _ ≤ sectionDeficitContractionFactor C ^ k * supportDeficit u x p (x + v) := hh
    _ ≤ sectionDeficitContractionFactor C ^ k * (2 * (L : ℝ) * r) :=
      mul_le_mul_of_nonneg_left hbase' (pow_nonneg hκ.le k)
    _ = _ := by ring

/-- Actual slope oscillation decays geometrically at dyadic Euclidean scales.
The decay factor is 2κ<1, where κ=C/(2C+1); no exponent is postulated. -/
theorem norm_subgradient_sub_le_dyadic
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    {S : Set (Space n)} (hSc : Convex ℝ S) {C : ℝ} (hC : 0 < C)
    (hcompare : ∀ x ∈ S, ∀ y ∈ S, ∀ p ∈ convexSubgradient u x,
      ∀ q ∈ convexSubgradient u y, supportDeficit u x p y ≤ C * supportDeficit u y q x)
    {x y p q : Space n} {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ S)
    (hp : p ∈ convexSubgradient u x) (hq : q ∈ convexSubgradient u y) (k : ℕ)
    (hy : ‖y - x‖ ≤ r * (1 / 2 : ℝ) ^ (k + 1)) :
    ‖q - p‖ ≤ 4 * (L : ℝ) * (2 * sectionDeficitContractionFactor C) ^ k := by
  let ρ : ℝ := r * (1 / 2 : ℝ) ^ (k + 1)
  let H : ℝ := 2 * (L : ℝ) * r * sectionDeficitContractionFactor C ^ k
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hκ := (sectionDeficitContractionFactor_pos_lt_half hC).1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hslope : q - p ∈ convexSubgradient (supportDeficit u x p) y := by
    intro z
    have hh := hq z
    dsimp [supportDeficit]
    simp only [inner_sub_left, inner_sub_right] at hh ⊢
    linarith
  have hupper : ∀ z ∈ closedBall y ρ,
      supportDeficit u x p z ≤ supportDeficit u x p y + H := by
    intro z hz
    have hzn : ‖z - y‖ ≤ ρ := hz
    have hdist : ‖z - x‖ ≤ r * (1 / 2 : ℝ) ^ k := by
      have htri := norm_sub_le_norm_sub_add_norm_sub z y x
      have hρeq : 2 * ρ = r * (1 / 2 : ℝ) ^ k := by dsimp [ρ]; rw [pow_succ]; ring
      change ‖y - x‖ ≤ ρ at hy
      linarith
    have hb := supportDeficit_le_at_dyadic_distance hLip hc hSc hC hcompare hr.le hball hp k hdist
    have hnonneg := supportDeficit_nonneg hp y
    change supportDeficit u x p z ≤ H at hb
    linarith
  have hn := norm_subgradient_le_of_ball_oscillation hslope hρ hH hupper
  have heq : H / ρ = 4 * (L : ℝ) * (2 * sectionDeficitContractionFactor C) ^ k := by
    apply (div_eq_iff hρ.ne').mpr
    have hpow : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    dsimp [H, ρ]
    rw [mul_pow, pow_succ]
    calc
      _ = (2 * (L : ℝ) * r * sectionDeficitContractionFactor C ^ k) *
          ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by rw [hpow, mul_one]
      _ = _ := by ring
  rw [heq] at hn
  exact hn

theorem dyadic_subgradient_decay_factor_lt_one {C : ℝ} (hC : 0 < C) :
    0 < 2 * sectionDeficitContractionFactor C ∧ 2 * sectionDeficitContractionFactor C < 1 := by
  have hκ := sectionDeficitContractionFactor_pos_lt_half hC
  constructor <;> linarith

end KLS
end

#print axioms KLS.supportDeficit_dyadic_le_on_convex_set
#print axioms KLS.supportDeficit_le_at_dyadic_distance
#print axioms KLS.norm_subgradient_sub_le_dyadic
#print axioms KLS.dyadic_subgradient_decay_factor_lt_one
