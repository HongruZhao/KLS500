import IteratedResolventDisplacement
import IteratedResolventSpectral

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem reciprocal_sqrt_step_le {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt (x+1) ≤ 2*(Real.sqrt (x+1)-Real.sqrt x) := by
  have hs : 0 < Real.sqrt (x+1) := Real.sqrt_pos.mpr (by linarith)
  apply (div_le_iff₀ hs).mpr
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt (show 0 ≤ x+1 by linarith),
    sq_nonneg (Real.sqrt (x+1)-Real.sqrt x)]

theorem finite_reciprocal_sqrt_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, 1/Real.sqrt ((j:ℝ)+2)) ≤
      2*(Real.sqrt ((m:ℝ)+1)-1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hh := reciprocal_sqrt_step_le (show 0 ≤ (m:ℝ)+1 by positivity)
    rw [Finset.sum_range_succ]
    have hh' : 1/Real.sqrt ((m:ℝ)+2) ≤
        2*(Real.sqrt ((m:ℝ)+2)-Real.sqrt ((m:ℝ)+1)) := by
      simpa only [show (m:ℝ)+1+1 = (m:ℝ)+2 by ring] using hh
    calc
      _ ≤ 2*(Real.sqrt ((m:ℝ)+1)-1) +
          2*(Real.sqrt ((m:ℝ)+2)-Real.sqrt ((m:ℝ)+1)) := add_le_add ih hh'
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, show (m:ℝ)+1+1 = (m:ℝ)+2 by ring]; ring

theorem resolvent_step_coefficient_factor {t B x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    t*(B/Real.sqrt (2*x*t)) =
      (B*Real.sqrt (2*t)/2)*(1/Real.sqrt x) := by
  rw [show 2*x*t = (2*t)*x by ring, Real.sqrt_mul (by positivity : 0 ≤ 2*t)]
  have hs := Real.sqrt_pos.mpr (show 0 < 2*t by positivity)
  have hx' := Real.sqrt_pos.mpr hx
  field_simp
  linear_combination (norm := ring_nf) -B * (Real.sq_sqrt (show 0 ≤ t*2 by positivity))

theorem finite_resolvent_displacement_coefficient_le {t B : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (m : ℕ) :
    2*Real.sqrt 2*B*Real.sqrt t +
      (∑ j ∈ Finset.range m, t*(B/Real.sqrt (2*((j:ℝ)+2)*t))) ≤
      Real.sqrt (2*t)*(1+Real.sqrt ((m:ℝ)+1))*B := by
  have he : (∑ j ∈ Finset.range m, t*(B/Real.sqrt (2*((j:ℝ)+2)*t))) =
      (B*Real.sqrt (2*t)/2)*(∑ j ∈ Finset.range m, 1/Real.sqrt ((j:ℝ)+2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact resolvent_step_coefficient_factor ht (by positivity)
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (finite_reciprocal_sqrt_sum_le m)
    (show 0 ≤ B*Real.sqrt (2*t)/2 by positivity)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hh ⊢
  nlinarith

theorem iterated_resolvent_contraction_certificate :
    (3200/3201 : ℝ)^4096 ≤ 2/7 := by
  have hblock : (3200/3201 : ℝ)^64 ≤ 1961/2000 := by norm_num
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (3200/3201 : ℝ)^64) hblock 64
  rw [← pow_mul] at hh
  exact hh.trans (by norm_num)

theorem iterated_resolvent_displacement_certificate {C : ℝ} (hC : 0 < C) :
    Real.sqrt (2*(C/3200))*(1+Real.sqrt ((4094:ℝ)+1)) ≤ (13/8)*Real.sqrt C := by
  have hroot : Real.sqrt (2*(C/3200)) = Real.sqrt C/40 := by
    rw [show 2*(C/3200) = C/(40^2) by ring, Real.sqrt_div hC.le,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 40)]
  have hbound : Real.sqrt ((4094:ℝ)+1) ≤ 64 := by
    have hh := Real.sqrt_le_sqrt (by norm_num : (4094:ℝ)+1 ≤ 4096)
    norm_num at hh ⊢
    exact hh
  rw [hroot]
  calc
    _ ≤ (Real.sqrt C/40)*(1+64) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (by positivity)
    _ = _ := by ring

end KLS.ConstantReduction
end
