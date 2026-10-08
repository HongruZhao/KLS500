import OptRankWeights

/-! Separate rational envelopes for cumulants and integrated energies.
The second cumulant uses its actual quadratic-eight estimate. -/
open scoped BigOperators
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS

def twentyEightHalfIntegralWeight (r : ℕ) : ℝ :=
    if r = 1 then (16000/5719 : ℝ) else
    if r = 2 then (4123/2000 : ℝ) else
    if r = 3 then (15913/10000 : ℝ) else
    if r = 4 then (13943/10000 : ℝ) else
    if r = 5 then (6411/5000 : ℝ) else
    if r = 6 then (12093/10000 : ℝ) else
    if r = 7 then (724/625 : ℝ) else
    if r = 8 then (11213/10000 : ℝ) else
    if r = 9 then (10933/10000 : ℝ) else
    if r = 10 then (10717/10000 : ℝ) else
    if r = 11 then (5273/5000 : ℝ) else
    if r = 12 then (10409/10000 : ℝ) else
    if r = 13 then (10297/10000 : ℝ) else
    if r = 14 then (2041/2000 : ℝ) else
    if r = 15 then (10129/10000 : ℝ) else
    if r = 16 then (2013/2000 : ℝ) else
    if r = 17 then (1001/1000 : ℝ) else
    if r = 18 then (9963/10000 : ℝ) else
    if r = 19 then (9923/10000 : ℝ) else
    if r = 20 then (618/625 : ℝ) else
    if r = 21 then (9857/10000 : ℝ) else
    if r = 22 then (983/1000 : ℝ) else
    if r = 23 then (4903/5000 : ℝ) else
    if r = 24 then (1957/2000 : ℝ) else
    if r = 25 then (4883/5000 : ℝ) else
    if r = 26 then (2437/2500 : ℝ) else
    if r = 27 then (2433/2500 : ℝ) else
    if r = 28 then (9717/10000 : ℝ) else
    if r = 29 then (9703/10000 : ℝ) else
    if r = 30 then (969/1000 : ℝ) else
    if r = 31 then (4839/5000 : ℝ) else
    if r = 32 then (9667/10000 : ℝ) else 1

def twentyEightHalfCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then 1 else if r = 2 then (8000/139707 : ℝ) else twentyEightHalfIntegralWeight r

def twentyEightHalfIntegralExcess (r : ℕ) : ℝ :=
    (if r = 1 then (10281/5719 : ℝ) else 0) +
    (if r = 2 then (2123/2000 : ℝ) else 0) +
    (if r = 3 then (5913/10000 : ℝ) else 0) +
    (if r = 4 then (3943/10000 : ℝ) else 0) +
    (if r = 5 then (1411/5000 : ℝ) else 0) +
    (if r = 6 then (2093/10000 : ℝ) else 0) +
    (if r = 7 then (99/625 : ℝ) else 0) +
    (if r = 8 then (1213/10000 : ℝ) else 0) +
    (if r = 9 then (933/10000 : ℝ) else 0) +
    (if r = 10 then (717/10000 : ℝ) else 0) +
    (if r = 11 then (273/5000 : ℝ) else 0) +
    (if r = 12 then (409/10000 : ℝ) else 0) +
    (if r = 13 then (297/10000 : ℝ) else 0) +
    (if r = 14 then (41/2000 : ℝ) else 0) +
    (if r = 15 then (129/10000 : ℝ) else 0) +
    (if r = 16 then (13/2000 : ℝ) else 0) +
    (if r = 17 then (1/1000 : ℝ) else 0)

def twentyEightHalfCumulantExcess (r : ℕ) : ℝ :=
    (if r = 3 then (5913/10000 : ℝ) else 0) +
    (if r = 4 then (3943/10000 : ℝ) else 0) +
    (if r = 5 then (1411/5000 : ℝ) else 0) +
    (if r = 6 then (2093/10000 : ℝ) else 0) +
    (if r = 7 then (99/625 : ℝ) else 0) +
    (if r = 8 then (1213/10000 : ℝ) else 0) +
    (if r = 9 then (933/10000 : ℝ) else 0) +
    (if r = 10 then (717/10000 : ℝ) else 0) +
    (if r = 11 then (273/5000 : ℝ) else 0) +
    (if r = 12 then (409/10000 : ℝ) else 0) +
    (if r = 13 then (297/10000 : ℝ) else 0) +
    (if r = 14 then (41/2000 : ℝ) else 0) +
    (if r = 15 then (129/10000 : ℝ) else 0) +
    (if r = 16 then (13/2000 : ℝ) else 0) +
    (if r = 17 then (1/1000 : ℝ) else 0)

def twentyEightHalfRankConvolution (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (r-2), twentyEightHalfIntegralWeight j * twentyEightHalfCumulantWeight (r-j)

def twentyEightHalfRootAllowance (r : ℕ) : ℝ :=
    if r = 2 then 0 else
    if r = 3 then (297/200 : ℝ) else
    if r = 4 then (2463/250 : ℝ) else
    if r = 5 then (14247/1000 : ℝ) else
    if r = 6 then (8811/500 : ℝ) else
    if r = 7 then (20619/1000 : ℝ) else
    if r = 8 then (23421/1000 : ℝ) else
    if r = 9 then (26109/1000 : ℝ) else
    if r = 10 then (7181/250 : ℝ) else
    if r = 11 then (7823/250 : ℝ) else
    if r = 12 then (16913/500 : ℝ) else
    if r = 13 then (36337/1000 : ℝ) else
    if r = 14 then (38831/1000 : ℝ) else
    if r = 15 then (5164/125 : ℝ) else
    if r = 16 then (21893/500 : ℝ) else
    if r = 17 then (11563/250 : ℝ) else
    if r = 18 then (4871/100 : ℝ) else
    if r = 19 then (51163/1000 : ℝ) else
    if r = 20 then (26807/500 : ℝ) else
    if r = 21 then (56061/1000 : ℝ) else
    if r = 22 then (58503/1000 : ℝ) else
    if r = 23 then (7618/125 : ℝ) else
    if r = 24 then (31691/500 : ℝ) else
    if r = 25 then (32909/500 : ℝ) else
    if r = 26 then (17063/250 : ℝ) else
    if r = 27 then (1767/25 : ℝ) else
    if r = 28 then (73107/1000 : ℝ) else
    if r = 29 then (75531/1000 : ℝ) else
    if r = 30 then (77951/1000 : ℝ) else
    if r = 31 then (10046/125 : ℝ) else
    if r = 32 then (82783/1000 : ℝ) else
    if r = 33 then (21299/250 : ℝ) else
    if r = 34 then (44633/500 : ℝ) else (31/12 : ℝ) * ((r : ℝ)+9/8)

theorem twentyEightHalfIntegralWeight_large {r : ℕ} (hr : 33 ≤ r) : twentyEightHalfIntegralWeight r = 1 := by
  simp only [twentyEightHalfIntegralWeight,
    ite_eq_right (show r ≠ 1 by omega),
    ite_eq_right (show r ≠ 2 by omega),
    ite_eq_right (show r ≠ 3 by omega),
    ite_eq_right (show r ≠ 4 by omega),
    ite_eq_right (show r ≠ 5 by omega),
    ite_eq_right (show r ≠ 6 by omega),
    ite_eq_right (show r ≠ 7 by omega),
    ite_eq_right (show r ≠ 8 by omega),
    ite_eq_right (show r ≠ 9 by omega),
    ite_eq_right (show r ≠ 10 by omega),
    ite_eq_right (show r ≠ 11 by omega),
    ite_eq_right (show r ≠ 12 by omega),
    ite_eq_right (show r ≠ 13 by omega),
    ite_eq_right (show r ≠ 14 by omega),
    ite_eq_right (show r ≠ 15 by omega),
    ite_eq_right (show r ≠ 16 by omega),
    ite_eq_right (show r ≠ 17 by omega),
    ite_eq_right (show r ≠ 18 by omega),
    ite_eq_right (show r ≠ 19 by omega),
    ite_eq_right (show r ≠ 20 by omega),
    ite_eq_right (show r ≠ 21 by omega),
    ite_eq_right (show r ≠ 22 by omega),
    ite_eq_right (show r ≠ 23 by omega),
    ite_eq_right (show r ≠ 24 by omega),
    ite_eq_right (show r ≠ 25 by omega),
    ite_eq_right (show r ≠ 26 by omega),
    ite_eq_right (show r ≠ 27 by omega),
    ite_eq_right (show r ≠ 28 by omega),
    ite_eq_right (show r ≠ 29 by omega),
    ite_eq_right (show r ≠ 30 by omega),
    ite_eq_right (show r ≠ 31 by omega),
    ite_eq_right (show r ≠ 32 by omega)]

theorem twentyEightHalfIntegralWeight_pos (r : ℕ) : 0 < twentyEightHalfIntegralWeight r := by
  by_cases hr : 33 ≤ r
  · rw [twentyEightHalfIntegralWeight_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentyEightHalfIntegralWeight]

theorem twentyEightHalfIntegralWeight_le_three (r : ℕ) : twentyEightHalfIntegralWeight r ≤ 3 := by
  by_cases hr : 33 ≤ r
  · rw [twentyEightHalfIntegralWeight_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentyEightHalfIntegralWeight]

theorem twentyEightHalfIntegralWeight_le_one {r : ℕ} (hr : 18 ≤ r) : twentyEightHalfIntegralWeight r ≤ 1 := by
  by_cases hlarge : 33 ≤ r
  · rw [twentyEightHalfIntegralWeight_large hlarge]
  · interval_cases r <;> norm_num [twentyEightHalfIntegralWeight]

theorem twentyEightHalfCumulantWeight_eq_integral {r : ℕ} (hr : 3 ≤ r) :
    twentyEightHalfCumulantWeight r = twentyEightHalfIntegralWeight r := by
  simp only [twentyEightHalfCumulantWeight, ite_eq_right (show r ≠ 1 by omega),
    ite_eq_right (show r ≠ 2 by omega)]

theorem twentyEightHalfCumulantWeight_pos (r : ℕ) : 0 < twentyEightHalfCumulantWeight r := by
  by_cases hr : 3 ≤ r
  · rw [twentyEightHalfCumulantWeight_eq_integral hr]
    exact twentyEightHalfIntegralWeight_pos r
  · interval_cases r <;> norm_num [twentyEightHalfCumulantWeight, twentyEightHalfIntegralWeight]

theorem twentyEightHalfCumulantWeight_le_three (r : ℕ) : twentyEightHalfCumulantWeight r ≤ 3 := by
  by_cases hr : 3 ≤ r
  · rw [twentyEightHalfCumulantWeight_eq_integral hr]
    exact twentyEightHalfIntegralWeight_le_three r
  · interval_cases r <;> norm_num [twentyEightHalfCumulantWeight, twentyEightHalfIntegralWeight]

theorem twentyEightHalfIntegralExcess_nonneg (r : ℕ) : 0 ≤ twentyEightHalfIntegralExcess r := by
  unfold twentyEightHalfIntegralExcess
  positivity

theorem twentyEightHalfIntegralExcess_large {r : ℕ} (hr : 18 ≤ r) : twentyEightHalfIntegralExcess r = 0 := by
  simp only [twentyEightHalfIntegralExcess,
    ite_eq_right (show r ≠ 1 by omega),
    ite_eq_right (show r ≠ 2 by omega),
    ite_eq_right (show r ≠ 3 by omega),
    ite_eq_right (show r ≠ 4 by omega),
    ite_eq_right (show r ≠ 5 by omega),
    ite_eq_right (show r ≠ 6 by omega),
    ite_eq_right (show r ≠ 7 by omega),
    ite_eq_right (show r ≠ 8 by omega),
    ite_eq_right (show r ≠ 9 by omega),
    ite_eq_right (show r ≠ 10 by omega),
    ite_eq_right (show r ≠ 11 by omega),
    ite_eq_right (show r ≠ 12 by omega),
    ite_eq_right (show r ≠ 13 by omega),
    ite_eq_right (show r ≠ 14 by omega),
    ite_eq_right (show r ≠ 15 by omega),
    ite_eq_right (show r ≠ 16 by omega),
    ite_eq_right (show r ≠ 17 by omega)]
  norm_num

theorem twentyEightHalfIntegralWeight_le_one_add_excess (r : ℕ) :
    twentyEightHalfIntegralWeight r ≤ 1 + twentyEightHalfIntegralExcess r := by
  by_cases hr : 33 ≤ r
  · rw [twentyEightHalfIntegralWeight_large hr, twentyEightHalfIntegralExcess_large (by omega : 18 ≤ r)]
    norm_num
  · interval_cases r <;> norm_num [twentyEightHalfCumulantWeight, twentyEightHalfIntegralWeight, twentyEightHalfIntegralExcess]

theorem sum_twentyEightHalfIntegralExcess_le (s : Finset ℕ) :
    (∑ j ∈ s, twentyEightHalfIntegralExcess j) ≤ 5 := by
  have hterm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (∑ j ∈ s, if j = k then a else 0) ≤ a := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> simp_all
  simp only [twentyEightHalfIntegralExcess, Finset.sum_add_distrib]
  linarith [
    hterm (10281/5719 : ℝ) (by norm_num) 1,
    hterm (2123/2000 : ℝ) (by norm_num) 2,
    hterm (5913/10000 : ℝ) (by norm_num) 3,
    hterm (3943/10000 : ℝ) (by norm_num) 4,
    hterm (1411/5000 : ℝ) (by norm_num) 5,
    hterm (2093/10000 : ℝ) (by norm_num) 6,
    hterm (99/625 : ℝ) (by norm_num) 7,
    hterm (1213/10000 : ℝ) (by norm_num) 8,
    hterm (933/10000 : ℝ) (by norm_num) 9,
    hterm (717/10000 : ℝ) (by norm_num) 10,
    hterm (273/5000 : ℝ) (by norm_num) 11,
    hterm (409/10000 : ℝ) (by norm_num) 12,
    hterm (297/10000 : ℝ) (by norm_num) 13,
    hterm (41/2000 : ℝ) (by norm_num) 14,
    hterm (129/10000 : ℝ) (by norm_num) 15,
    hterm (13/2000 : ℝ) (by norm_num) 16,
    hterm (1/1000 : ℝ) (by norm_num) 17]

theorem twentyEightHalfCumulantExcess_nonneg (r : ℕ) : 0 ≤ twentyEightHalfCumulantExcess r := by
  unfold twentyEightHalfCumulantExcess
  positivity

theorem twentyEightHalfCumulantExcess_large {r : ℕ} (hr : 18 ≤ r) : twentyEightHalfCumulantExcess r = 0 := by
  simp only [twentyEightHalfCumulantExcess,
    ite_eq_right (show r ≠ 3 by omega),
    ite_eq_right (show r ≠ 4 by omega),
    ite_eq_right (show r ≠ 5 by omega),
    ite_eq_right (show r ≠ 6 by omega),
    ite_eq_right (show r ≠ 7 by omega),
    ite_eq_right (show r ≠ 8 by omega),
    ite_eq_right (show r ≠ 9 by omega),
    ite_eq_right (show r ≠ 10 by omega),
    ite_eq_right (show r ≠ 11 by omega),
    ite_eq_right (show r ≠ 12 by omega),
    ite_eq_right (show r ≠ 13 by omega),
    ite_eq_right (show r ≠ 14 by omega),
    ite_eq_right (show r ≠ 15 by omega),
    ite_eq_right (show r ≠ 16 by omega),
    ite_eq_right (show r ≠ 17 by omega)]
  norm_num

theorem twentyEightHalfCumulantWeight_le_one_add_excess (r : ℕ) :
    twentyEightHalfCumulantWeight r ≤ 1 + twentyEightHalfCumulantExcess r := by
  by_cases hr : 33 ≤ r
  · rw [twentyEightHalfCumulantWeight_eq_integral (by omega : 3 ≤ r),
      twentyEightHalfIntegralWeight_large hr, twentyEightHalfCumulantExcess_large (by omega : 18 ≤ r)]
    norm_num
  · interval_cases r <;> norm_num [twentyEightHalfCumulantWeight, twentyEightHalfIntegralWeight, twentyEightHalfCumulantExcess]

theorem sum_twentyEightHalfCumulantExcess_le (s : Finset ℕ) :
    (∑ j ∈ s, twentyEightHalfCumulantExcess j) ≤ (21/10 : ℝ) := by
  have hterm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (∑ j ∈ s, if j = k then a else 0) ≤ a := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> simp_all
  simp only [twentyEightHalfCumulantExcess, Finset.sum_add_distrib]
  linarith [
    hterm (5913/10000 : ℝ) (by norm_num) 3,
    hterm (3943/10000 : ℝ) (by norm_num) 4,
    hterm (1411/5000 : ℝ) (by norm_num) 5,
    hterm (2093/10000 : ℝ) (by norm_num) 6,
    hterm (99/625 : ℝ) (by norm_num) 7,
    hterm (1213/10000 : ℝ) (by norm_num) 8,
    hterm (933/10000 : ℝ) (by norm_num) 9,
    hterm (717/10000 : ℝ) (by norm_num) 10,
    hterm (273/5000 : ℝ) (by norm_num) 11,
    hterm (409/10000 : ℝ) (by norm_num) 12,
    hterm (297/10000 : ℝ) (by norm_num) 13,
    hterm (41/2000 : ℝ) (by norm_num) 14,
    hterm (129/10000 : ℝ) (by norm_num) 15,
    hterm (13/2000 : ℝ) (by norm_num) 16,
    hterm (1/1000 : ℝ) (by norm_num) 17]

theorem twentyEightHalfRankConvolution_nonneg (r : ℕ) : 0 ≤ twentyEightHalfRankConvolution r := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (twentyEightHalfIntegralWeight_pos j).le
    (twentyEightHalfCumulantWeight_pos (r-j)).le

theorem twentyEightHalfRootAllowance_large {r : ℕ} (hr : 35 ≤ r) :
    twentyEightHalfRootAllowance r = (31/12 : ℝ) * ((r : ℝ)+9/8) := by
  simp only [twentyEightHalfRootAllowance,
    ite_eq_right (show r ≠ 2 by omega),
    ite_eq_right (show r ≠ 3 by omega),
    ite_eq_right (show r ≠ 4 by omega),
    ite_eq_right (show r ≠ 5 by omega),
    ite_eq_right (show r ≠ 6 by omega),
    ite_eq_right (show r ≠ 7 by omega),
    ite_eq_right (show r ≠ 8 by omega),
    ite_eq_right (show r ≠ 9 by omega),
    ite_eq_right (show r ≠ 10 by omega),
    ite_eq_right (show r ≠ 11 by omega),
    ite_eq_right (show r ≠ 12 by omega),
    ite_eq_right (show r ≠ 13 by omega),
    ite_eq_right (show r ≠ 14 by omega),
    ite_eq_right (show r ≠ 15 by omega),
    ite_eq_right (show r ≠ 16 by omega),
    ite_eq_right (show r ≠ 17 by omega),
    ite_eq_right (show r ≠ 18 by omega),
    ite_eq_right (show r ≠ 19 by omega),
    ite_eq_right (show r ≠ 20 by omega),
    ite_eq_right (show r ≠ 21 by omega),
    ite_eq_right (show r ≠ 22 by omega),
    ite_eq_right (show r ≠ 23 by omega),
    ite_eq_right (show r ≠ 24 by omega),
    ite_eq_right (show r ≠ 25 by omega),
    ite_eq_right (show r ≠ 26 by omega),
    ite_eq_right (show r ≠ 27 by omega),
    ite_eq_right (show r ≠ 28 by omega),
    ite_eq_right (show r ≠ 29 by omega),
    ite_eq_right (show r ≠ 30 by omega),
    ite_eq_right (show r ≠ 31 by omega),
    ite_eq_right (show r ≠ 32 by omega),
    ite_eq_right (show r ≠ 33 by omega),
    ite_eq_right (show r ≠ 34 by omega)]

theorem twentyEightHalfRootAllowance_nonneg (r : ℕ) : 0 ≤ twentyEightHalfRootAllowance r := by
  by_cases hr : 35 ≤ r
  · rw [twentyEightHalfRootAllowance_large hr]
    positivity
  · interval_cases r <;> norm_num [twentyEightHalfRootAllowance]

end KLS
end
