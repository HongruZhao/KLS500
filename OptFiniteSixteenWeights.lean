import KLS.CumulantFactorialMajorant

/-! Explicit finite-rank compact and integrated energy bounds, normalized
by the squared factorial. Every numerical entry is checked below. -/
open scoped BigOperators
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS

def finiteSixteenCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then 1 else
  if r = 2 then 2 else
  if r = 3 then 576 else
  if r = 4 then 15497 else
  if r = 5 then 404018 else
  if r = 6 then 10531640 else
  if r = 7 then 275717509 else
  if r = 8 then 7251332367 else
  if r = 9 then 191476234547 else
  if r = 10 then 5073054328799 else
  if r = 11 then 134779914445677 else
  if r = 12 then 3588957774654180 else
  if r = 13 then 95747108185763062 else
  if r = 14 then 2558334528765306914 else
  if r = 15 then 68446391082489043235 else
  if r = 16 then 1833217393350109324897 else 1

@[simp] theorem finiteSixteenCumulantWeight_1 : finiteSixteenCumulantWeight 1 = 1 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_2 : finiteSixteenCumulantWeight 2 = 2 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_3 : finiteSixteenCumulantWeight 3 = 576 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_4 : finiteSixteenCumulantWeight 4 = 15497 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_5 : finiteSixteenCumulantWeight 5 = 404018 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_6 : finiteSixteenCumulantWeight 6 = 10531640 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_7 : finiteSixteenCumulantWeight 7 = 275717509 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_8 : finiteSixteenCumulantWeight 8 = 7251332367 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_9 : finiteSixteenCumulantWeight 9 = 191476234547 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_10 : finiteSixteenCumulantWeight 10 = 5073054328799 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_11 : finiteSixteenCumulantWeight 11 = 134779914445677 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_12 : finiteSixteenCumulantWeight 12 = 3588957774654180 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_13 : finiteSixteenCumulantWeight 13 = 95747108185763062 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_14 : finiteSixteenCumulantWeight 14 = 2558334528765306914 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_15 : finiteSixteenCumulantWeight 15 = 68446391082489043235 := by
  norm_num [finiteSixteenCumulantWeight]

@[simp] theorem finiteSixteenCumulantWeight_16 : finiteSixteenCumulantWeight 16 = 1833217393350109324897 := by
  norm_num [finiteSixteenCumulantWeight]

theorem finiteSixteenCumulantWeight_nonneg (r : ℕ) : 0 ≤ finiteSixteenCumulantWeight r := by
  by_cases hr : 17 ≤ r
  · simp only [finiteSixteenCumulantWeight,
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
    ite_eq_right (show r ≠ 16 by omega)]
    norm_num
  · interval_cases r <;> norm_num [finiteSixteenCumulantWeight]

def finiteSixteenIntegralWeight (r : ℕ) : ℝ :=
  if r = 1 then 8 else
  if r = 2 then 168 else
  if r = 3 then 3696 else
  if r = 4 then 87904 else
  if r = 5 then 2173365 else
  if r = 6 then 55000936 else
  if r = 7 then 1413353958 else
  if r = 8 then 36706730934 else
  if r = 9 then 960672113684 else
  if r = 10 then 25286536358772 else
  if r = 11 then 668497976062721 else
  if r = 12 then 17733206472404514 else
  if r = 13 then 471674809713777006 else
  if r = 14 then 12572894569778594217 else
  if r = 15 then 335728769836041419919 else
  if r = 16 then 8977710028854834970293 else 1

@[simp] theorem finiteSixteenIntegralWeight_1 : finiteSixteenIntegralWeight 1 = 8 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_2 : finiteSixteenIntegralWeight 2 = 168 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_3 : finiteSixteenIntegralWeight 3 = 3696 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_4 : finiteSixteenIntegralWeight 4 = 87904 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_5 : finiteSixteenIntegralWeight 5 = 2173365 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_6 : finiteSixteenIntegralWeight 6 = 55000936 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_7 : finiteSixteenIntegralWeight 7 = 1413353958 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_8 : finiteSixteenIntegralWeight 8 = 36706730934 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_9 : finiteSixteenIntegralWeight 9 = 960672113684 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_10 : finiteSixteenIntegralWeight 10 = 25286536358772 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_11 : finiteSixteenIntegralWeight 11 = 668497976062721 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_12 : finiteSixteenIntegralWeight 12 = 17733206472404514 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_13 : finiteSixteenIntegralWeight 13 = 471674809713777006 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_14 : finiteSixteenIntegralWeight 14 = 12572894569778594217 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_15 : finiteSixteenIntegralWeight 15 = 335728769836041419919 := by
  norm_num [finiteSixteenIntegralWeight]

@[simp] theorem finiteSixteenIntegralWeight_16 : finiteSixteenIntegralWeight 16 = 8977710028854834970293 := by
  norm_num [finiteSixteenIntegralWeight]

theorem finiteSixteenIntegralWeight_nonneg (r : ℕ) : 0 ≤ finiteSixteenIntegralWeight r := by
  by_cases hr : 17 ≤ r
  · simp only [finiteSixteenIntegralWeight,
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
    ite_eq_right (show r ≠ 16 by omega)]
    norm_num
  · interval_cases r <;> norm_num [finiteSixteenIntegralWeight]

def finiteSixteenRootAllowance (r : ℕ) : ℝ :=
  if r = 1 then 0 else
  if r = 2 then 0 else
  if r = 3 then 52 else
  if r = 4 then 6046 else
  if r = 5 then 245280 else
  if r = 6 then 8412358 else
  if r = 7 then 269642304 else
  if r = 8 then 8335027830 else
  if r = 9 then 251903469387 else
  if r = 10 then 7496770329469 else
  if r = 11 then 220616758063781 else
  if r = 12 then 6436834021841962 else
  if r = 13 then 186528551827979727 else
  if r = 14 then 5375268186105359381 else
  if r = 15 then 154182244908659316125 else
  if r = 16 then 4405028618686858702901 else 1

@[simp] theorem finiteSixteenRootAllowance_1 : finiteSixteenRootAllowance 1 = 0 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_2 : finiteSixteenRootAllowance 2 = 0 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_3 : finiteSixteenRootAllowance 3 = 52 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_4 : finiteSixteenRootAllowance 4 = 6046 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_5 : finiteSixteenRootAllowance 5 = 245280 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_6 : finiteSixteenRootAllowance 6 = 8412358 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_7 : finiteSixteenRootAllowance 7 = 269642304 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_8 : finiteSixteenRootAllowance 8 = 8335027830 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_9 : finiteSixteenRootAllowance 9 = 251903469387 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_10 : finiteSixteenRootAllowance 10 = 7496770329469 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_11 : finiteSixteenRootAllowance 11 = 220616758063781 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_12 : finiteSixteenRootAllowance 12 = 6436834021841962 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_13 : finiteSixteenRootAllowance 13 = 186528551827979727 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_14 : finiteSixteenRootAllowance 14 = 5375268186105359381 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_15 : finiteSixteenRootAllowance 15 = 154182244908659316125 := by
  norm_num [finiteSixteenRootAllowance]

@[simp] theorem finiteSixteenRootAllowance_16 : finiteSixteenRootAllowance 16 = 4405028618686858702901 := by
  norm_num [finiteSixteenRootAllowance]

theorem finiteSixteenRootAllowance_nonneg (r : ℕ) : 0 ≤ finiteSixteenRootAllowance r := by
  by_cases hr : 17 ≤ r
  · simp only [finiteSixteenRootAllowance,
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
    ite_eq_right (show r ≠ 16 by omega)]
    norm_num
  · interval_cases r <;> norm_num [finiteSixteenRootAllowance]

def finiteSixteenRankConvolution (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (r-2), finiteSixteenIntegralWeight j * finiteSixteenCumulantWeight (r-j)

theorem finiteSixteenRankConvolution_nonneg (r : ℕ) : 0 ≤ finiteSixteenRankConvolution r := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (finiteSixteenIntegralWeight_nonneg j)
    (finiteSixteenCumulantWeight_nonneg (r-j))

end KLS
end
