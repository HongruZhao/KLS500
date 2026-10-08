import KLS.WeightedL1Compactness

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_average_sub_value_le_weighted_error
    {w h χ κ : Space n → ℝ} (hw : Continuous w) (hh : Continuous h)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hκ0 : ∀ x, 0 ≤ κ x) (hκmass : (∫ x, κ x) = 1)
    (hχone : ∀ x ∈ tsupport κ, χ x = 1)
    {B d : ℝ} (hB : 0 ≤ B) (hκB : ∀ x, κ x ≤ B)
    {c : Space n} (hosc : ∀ x ∈ tsupport κ, |h x - h c| ≤ d) :
    |(∫ x, w x * κ x) - h c| ≤ B * (∫ x, χ x * |w x - h x|) + d := by
  have hE : Integrable (fun x => χ x * |w x - h x|) :=
    (hχ.mul (hw.sub hh).abs).integrable_of_hasCompactSupport hχc.mul_right
  have hκi : Integrable κ volume := hκ.integrable_of_hasCompactSupport hκc
  have hwi : Integrable (fun x => w x * κ x) :=
    (hw.mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  have hH := (hE.const_mul B).add (hκi.const_mul d)
  have hp (x : Space n) : |(w x - h c) * κ x| ≤ B * (χ x * |w x - h x|) + d * κ x := by
    by_cases hx : x ∈ tsupport κ
    · rw [hχone x hx, one_mul, abs_mul, abs_of_nonneg (hκ0 x)]
      have he : |w x - h c| ≤ |w x - h x| + d :=
        (abs_sub_le (w x) (h x) (h c)).trans (add_le_add (le_refl _) (hosc x hx))
      have hm := mul_le_mul_of_nonneg_right he (hκ0 x)
      have hb := mul_le_mul_of_nonneg_left (hκB x) (abs_nonneg (w x - h x))
      nlinarith
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, abs_zero, mul_zero, add_zero]
      exact mul_nonneg hB (mul_nonneg (hχ0 x) (abs_nonneg _))
  have hi := norm_integral_le_of_norm_le (f := fun x => (w x - h c) * κ x) hH
    (Eventually.of_forall hp)
  change |∫ x, (w x - h c) * κ x| ≤ _ at hi
  have hid : (∫ x, (w x - h c) * κ x) = (∫ x, w x * κ x) - h c := by
    simp_rw [sub_mul]
    rw [integral_sub hwi (hκi.const_mul (h c)), integral_const_mul, hκmass, mul_one]
  rw [hid] at hi
  convert hi using 1
  simp only [Pi.add_apply]
  rw [integral_add (hE.const_mul B) (hκi.const_mul d), integral_const_mul, integral_const_mul,
    hκmass, mul_one]

lemma average_gap_le_weighted_gap
    {w v χ κ : Space n → ℝ} (hw : Continuous w) (hv : Continuous v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hχone : ∀ x ∈ tsupport κ, χ x = 1)
    (hgap : ∀ x, 0 ≤ χ x * (w x - v x)) {B : ℝ} (hB : 0 ≤ B) (hκB : ∀ x, κ x ≤ B) :
    (∫ x, w x * κ x) - (∫ x, v x * κ x) ≤ B * (∫ x, χ x * (w x - v x)) := by
  have hwi : Integrable (fun x => w x * κ x) := (hw.mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  have hvi : Integrable (fun x => v x * κ x) := (hv.mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  have hE : Integrable (fun x => χ x * (w x - v x)) :=
    (hχ.mul (hw.sub hv)).integrable_of_hasCompactSupport hχc.mul_right
  have hleft : (∫ x, w x * κ x) - (∫ x, v x * κ x) = ∫ x, (w x - v x) * κ x := by
    simp_rw [sub_mul]
    exact (integral_sub hwi hvi).symm
  rw [hleft, ← integral_const_mul]
  have hdi : Integrable (fun x => (w x - v x) * κ x) :=
    ((hw.sub hv).mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  apply integral_mono hdi (hE.const_mul B)
  intro x
  dsimp only
  by_cases hx : x ∈ tsupport κ
  · have hd0 := hgap x
    rw [hχone x hx, one_mul] at hd0 ⊢
    nlinarith [mul_le_mul_of_nonneg_left (hκB x) hd0]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    exact mul_nonneg hB (hgap x)

/-- A true upper primal average and lower dual average squeeze the actual
point value by two weighted integral errors and the limit oscillation. -/
theorem abs_primal_sub_limit_le_weighted_average_errors
    {w v h χ κ : Space n → ℝ} (hw : Continuous w) (hv : Continuous v) (hh : Continuous h)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hκ0 : ∀ x, 0 ≤ κ x) (hκmass : (∫ x, κ x) = 1)
    (hχone : ∀ x ∈ tsupport κ, χ x = 1)
    (hgap : ∀ x, 0 ≤ χ x * (w x - v x))
    {B d e : ℝ} (hB : 0 ≤ B) (hκB : ∀ x, κ x ≤ B)
    {c : Space n} (hosc : ∀ x ∈ tsupport κ, |h x - h c| ≤ d)
    (hupper : w c ≤ (∫ x, w x * κ x) + e)
    (hlower : (∫ x, v x * κ x) - e ≤ v c) (hvw : v c ≤ w c) :
    |w c - h c| ≤ B * ((∫ x, χ x * |w x - h x|) + (∫ x, χ x * (w x - v x))) + d + e := by
  have ha := abs_average_sub_value_le_weighted_error hw hh hχ hχc hκ hκc
    hχ0 hκ0 hκmass hχone hB hκB hosc
  have hg := average_gap_le_weighted_gap hw hv hχ hχc hκ hκc hχone hgap hB hκB
  have hg0 : 0 ≤ (∫ x, χ x * (w x - v x)) := integral_nonneg hgap
  have hBg : 0 ≤ B * (∫ x, χ x * (w x - v x)) := mul_nonneg hB hg0
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  apply abs_le.mpr
  constructor <;> nlinarith

end KLS
end
