import KLS.CumulantFactorialMajorant

/-! Exact rational finite-rank envelopes using positive cardinality weights. -/
open scoped BigOperators
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS

def rankCauchyCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then 1 else
  if r = 2 then 2 else
  if r = 3 then 576 else
  if r = 4 then 15095 else
  if r = 5 then 390472 else
  if r = 6 then 10115145 else
  if r = 7 then 263279186 else
  if r = 8 then 6886667254 else
  if r = 9 then 180917719198 else
  if r = 10 then 4770076873608 else
  if r = 11 then 126144021805887 else
  if r = 12 then 3344009848952617 else
  if r = 13 then 88828670835961446 else
  if r = 14 then 2363571835899732976 else
  if r = 15 then 62978265848271852909 else
  if r = 16 then 1680049546678489114313 else 1

@[simp] theorem rankCauchyCumulantWeight_1 : rankCauchyCumulantWeight 1 = 1 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_2 : rankCauchyCumulantWeight 2 = 2 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_3 : rankCauchyCumulantWeight 3 = 576 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_4 : rankCauchyCumulantWeight 4 = 15095 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_5 : rankCauchyCumulantWeight 5 = 390472 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_6 : rankCauchyCumulantWeight 6 = 10115145 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_7 : rankCauchyCumulantWeight 7 = 263279186 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_8 : rankCauchyCumulantWeight 8 = 6886667254 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_9 : rankCauchyCumulantWeight 9 = 180917719198 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_10 : rankCauchyCumulantWeight 10 = 4770076873608 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_11 : rankCauchyCumulantWeight 11 = 126144021805887 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_12 : rankCauchyCumulantWeight 12 = 3344009848952617 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_13 : rankCauchyCumulantWeight 13 = 88828670835961446 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_14 : rankCauchyCumulantWeight 14 = 2363571835899732976 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_15 : rankCauchyCumulantWeight 15 = 62978265848271852909 := by
  norm_num [rankCauchyCumulantWeight]

@[simp] theorem rankCauchyCumulantWeight_16 : rankCauchyCumulantWeight 16 = 1680049546678489114313 := by
  norm_num [rankCauchyCumulantWeight]

theorem rankCauchyCumulantWeight_nonneg (r : ℕ) : 0 ≤ rankCauchyCumulantWeight r := by
  unfold rankCauchyCumulantWeight
  positivity

def rankCauchyIntegralWeight (r : ℕ) : ℝ :=
  if r = 1 then 8 else
  if r = 2 then 168 else
  if r = 3 then 3696 else
  if r = 4 then 86966 else
  if r = 5 then 2128624 else
  if r = 6 then 53402740 else
  if r = 7 then 1361956461 else
  if r = 8 then 35136280713 else
  if r = 9 then 914049274776 else
  if r = 10 then 23926869218616 else
  if r = 11 then 629312219941026 else
  if r = 12 then 16613060726730469 else
  if r = 13 then 439849748791469939 else
  if r = 14 then 11672897433513289422 else
  if r = 15 then 310369851048487042028 else
  if r = 16 then 8265293523595293188455 else 1

@[simp] theorem rankCauchyIntegralWeight_1 : rankCauchyIntegralWeight 1 = 8 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_2 : rankCauchyIntegralWeight 2 = 168 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_3 : rankCauchyIntegralWeight 3 = 3696 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_4 : rankCauchyIntegralWeight 4 = 86966 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_5 : rankCauchyIntegralWeight 5 = 2128624 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_6 : rankCauchyIntegralWeight 6 = 53402740 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_7 : rankCauchyIntegralWeight 7 = 1361956461 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_8 : rankCauchyIntegralWeight 8 = 35136280713 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_9 : rankCauchyIntegralWeight 9 = 914049274776 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_10 : rankCauchyIntegralWeight 10 = 23926869218616 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_11 : rankCauchyIntegralWeight 11 = 629312219941026 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_12 : rankCauchyIntegralWeight 12 = 16613060726730469 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_13 : rankCauchyIntegralWeight 13 = 439849748791469939 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_14 : rankCauchyIntegralWeight 14 = 11672897433513289422 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_15 : rankCauchyIntegralWeight 15 = 310369851048487042028 := by
  norm_num [rankCauchyIntegralWeight]

@[simp] theorem rankCauchyIntegralWeight_16 : rankCauchyIntegralWeight 16 = 8265293523595293188455 := by
  norm_num [rankCauchyIntegralWeight]

theorem rankCauchyIntegralWeight_nonneg (r : ℕ) : 0 ≤ rankCauchyIntegralWeight r := by
  unfold rankCauchyIntegralWeight
  positivity

def rankCauchyRootAllowance (r : ℕ) : ℝ :=
  if r = 1 then 0 else
  if r = 2 then 0 else
  if r = 3 then 52 else
  if r = 4 then 5242 else
  if r = 5 then 219574 else
  if r = 6 then 7640110 else
  if r = 7 then 246313938 else
  if r = 8 then 7628055772 else
  if r = 9 then 230477073433 else
  if r = 10 then 6849067857205 else
  if r = 11 then 201116131021781 else
  if r = 12 then 5852091460047527 else
  if r = 13 then 169088444880642867 else
  if r = 14 then 4857566669124786733 else
  if r = 15 then 138881223844675928990 else
  if r = 16 then 3954717800758527692520 else 1

@[simp] theorem rankCauchyRootAllowance_1 : rankCauchyRootAllowance 1 = 0 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_2 : rankCauchyRootAllowance 2 = 0 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_3 : rankCauchyRootAllowance 3 = 52 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_4 : rankCauchyRootAllowance 4 = 5242 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_5 : rankCauchyRootAllowance 5 = 219574 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_6 : rankCauchyRootAllowance 6 = 7640110 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_7 : rankCauchyRootAllowance 7 = 246313938 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_8 : rankCauchyRootAllowance 8 = 7628055772 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_9 : rankCauchyRootAllowance 9 = 230477073433 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_10 : rankCauchyRootAllowance 10 = 6849067857205 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_11 : rankCauchyRootAllowance 11 = 201116131021781 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_12 : rankCauchyRootAllowance 12 = 5852091460047527 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_13 : rankCauchyRootAllowance 13 = 169088444880642867 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_14 : rankCauchyRootAllowance 14 = 4857566669124786733 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_15 : rankCauchyRootAllowance 15 = 138881223844675928990 := by
  norm_num [rankCauchyRootAllowance]

@[simp] theorem rankCauchyRootAllowance_16 : rankCauchyRootAllowance 16 = 3954717800758527692520 := by
  norm_num [rankCauchyRootAllowance]

theorem rankCauchyRootAllowance_nonneg (r : ℕ) : 0 ≤ rankCauchyRootAllowance r := by
  unfold rankCauchyRootAllowance
  positivity

def rankCauchyWeight (r j : ℕ) : ℝ :=
  if r = 3 then if j = 1 then 64 else 1 else
  if r = 4 then if j = 1 then 64 else if j = 2 then 18 else 1 else
  if r = 5 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 16 else 1 else
  if r = 6 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 16 else 1 else
  if r = 7 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 54 else if j = 4 then 51 else if j = 5 then 15 else 1 else
  if r = 8 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 51 else if j = 5 then 49 else if j = 6 then 15 else 1 else
  if r = 9 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 51 else if j = 5 then 49 else if j = 6 then 48 else if j = 7 then 15 else 1 else
  if r = 10 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 50 else if j = 5 then 49 else if j = 6 then 48 else if j = 7 then 48 else if j = 8 then 15 else 1 else
  if r = 11 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 50 else if j = 5 then 49 else if j = 6 then 48 else if j = 7 then 47 else if j = 8 then 47 else if j = 9 then 15 else 1 else
  if r = 12 then if j = 1 then 64 else if j = 2 then 58 else if j = 3 then 53 else if j = 4 then 50 else if j = 5 then 48 else if j = 6 then 47 else if j = 7 then 47 else if j = 8 then 47 else if j = 9 then 47 else if j = 10 then 14 else 1 else
  if r = 13 then if j = 1 then 64 else if j = 2 then 57 else if j = 3 then 52 else if j = 4 then 50 else if j = 5 then 48 else if j = 6 then 47 else if j = 7 then 46 else if j = 8 then 46 else if j = 9 then 46 else if j = 10 then 46 else if j = 11 then 14 else 1 else
  if r = 14 then if j = 1 then 64 else if j = 2 then 57 else if j = 3 then 52 else if j = 4 then 49 else if j = 5 then 48 else if j = 6 then 47 else if j = 7 then 46 else if j = 8 then 46 else if j = 9 then 46 else if j = 10 then 46 else if j = 11 then 46 else if j = 12 then 14 else 1 else
  if r = 15 then if j = 1 then 64 else if j = 2 then 57 else if j = 3 then 52 else if j = 4 then 49 else if j = 5 then 47 else if j = 6 then 46 else if j = 7 then 46 else if j = 8 then 45 else if j = 9 then 45 else if j = 10 then 45 else if j = 11 then 46 else if j = 12 then 46 else if j = 13 then 14 else 1 else
  if r = 16 then if j = 1 then 64 else if j = 2 then 57 else if j = 3 then 52 else if j = 4 then 49 else if j = 5 then 47 else if j = 6 then 46 else if j = 7 then 45 else if j = 8 then 45 else if j = 9 then 45 else if j = 10 then 45 else if j = 11 then 45 else if j = 12 then 46 else if j = 13 then 46 else if j = 14 then 14 else 1 else
  1

theorem rankCauchyWeight_pos (r j : ℕ) : 0 < rankCauchyWeight r j := by
  unfold rankCauchyWeight
  positivity

def rankCauchyConvolution (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (r-2), rankCauchyWeight r j) *
  (∑ j ∈ Finset.Icc 1 (r-2), rankCauchyIntegralWeight j * rankCauchyCumulantWeight (r-j) / rankCauchyWeight r j)

theorem rankCauchyConvolution_nonneg (r : ℕ) : 0 ≤ rankCauchyConvolution r := by
  apply mul_nonneg
  · exact Finset.sum_nonneg fun j _ => (rankCauchyWeight_pos r j).le
  · exact Finset.sum_nonneg fun j _ => div_nonneg
      (mul_nonneg (rankCauchyIntegralWeight_nonneg j) (rankCauchyCumulantWeight_nonneg (r-j)))
      (rankCauchyWeight_pos r j).le

end KLS
end
