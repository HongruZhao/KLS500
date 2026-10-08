import KLS.WeightedResolventSquarePairBound

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS

/-- One halving step of the resolvent estimate costs at most B sqrt(a). -/
theorem resolvent_half_step_coefficient_le {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    (a-a/2)*(B/Real.sqrt (2*a)+B/Real.sqrt (2*(a/2))) ≤ B*Real.sqrt a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hm : Real.sqrt a ≤ Real.sqrt (2*a) := Real.sqrt_le_sqrt (by linarith)
  have hd : B/Real.sqrt (2*a) ≤ B/Real.sqrt a := div_le_div_of_nonneg_left hB hs hm
  rw [show 2*(a/2)=a by ring]
  calc
    _ ≤ (a-a/2)*(B/Real.sqrt a+B/Real.sqrt a) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hd le_rfl) (by linarith)
    _ = B*Real.sqrt a := by
      field_simp
      nlinarith [Real.sq_sqrt ha.le]

/-- A convenient rational geometric majorant for dyadic square roots. -/
theorem sqrt_half_le_three_quarters {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a/2) ≤ (3/4 : ℝ)*Real.sqrt a := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ (3/4 : ℝ)*Real.sqrt a)).1
  rw [Real.sq_sqrt (by positivity : 0 ≤ a/2),mul_pow,Real.sq_sqrt ha]
  nlinarith

/-- Every actual dyadic time has the geometric square-root estimate. -/
theorem sqrt_dyadic_time_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Real.sqrt (t/2^k) ≤ Real.sqrt t*(3/4 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : t/2^(k+1)=(t/2^k)/2 := by rw [pow_succ,div_mul_eq_div_div]
    rw [he]
    calc
      _ ≤ (3/4 : ℝ)*Real.sqrt (t/2^k) := sqrt_half_le_three_quarters (by positivity)
      _ ≤ (3/4 : ℝ)*(Real.sqrt t*(3/4 : ℝ)^k) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ];ring

/-- Summable actual successive differences control the limit, with a simple
universal constant for the geometric majorant used above. -/
theorem abs_limit_sub_zero_le_of_three_quarters_steps {F : ℕ → ℝ} {L C : ℝ}
    (hC : 0 ≤ C) (hlim : Tendsto F atTop (𝓝 L))
    (hstep : ∀ k, |F (k + 1) - F k| ≤ C * (3 / 4 : ℝ) ^ k) : |L-F 0| ≤ 4*C := by
  have hb (k : ℕ) : |F k-F 0| ≤ 4*C*(1-(3/4 : ℝ)^k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = |(F (k+1)-F k)+(F k-F 0)| := by congr 1;ring
        _ ≤ |F (k+1)-F k|+|F k-F 0| := abs_add_le _ _
        _ ≤ C*(3/4 : ℝ)^k+4*C*(1-(3/4 : ℝ)^k) := add_le_add (hstep k) ih
        _ = _ := by rw [pow_succ];ring
  apply le_of_tendsto' ((hlim.sub_const (F 0)).abs)
  intro k
  exact (hb k).trans (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) k])

end KLS
end
