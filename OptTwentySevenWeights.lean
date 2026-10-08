import OptRankCauchyWeights
import OptRankWeights

/-! Separate compact and integrated envelopes with exponential base 27. -/
open scoped BigOperators
set_option maxHeartbeats 3000000
noncomputable section
namespace KLS

def twentySevenCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then (2000/1161 : ℝ) else
  if r = 2 then (4000/31347 : ℝ) else
  if r = 3 then (128000/94041 : ℝ) else
  if r = 4 then (30190000/22851963 : ℝ) else
  if r = 5 then (780944000/617003001 : ℝ) else
  if r = 6 then (749270000/617003001 : ℝ) else
  if r = 7 then (526558372000/449795187729 : ℝ) else
  if r = 8 then (13773334508000/12144470068683 : ℝ) else
  if r = 9 then (361835438396000/327900691854441 : ℝ) else
  if r = 10 then (1060017083024000/983702075563323 : ℝ) else
  if r = 11 then (84096014537258000/79679868120629163 : ℝ) else
  if r = 12 then (6688019697905234000/6454069317770962203 : ℝ) else
  if r = 13 then (59219113890640964000/58086623859938659827 : ℝ) else
  if r = 14 then (4727143671799465952000/4705016532655031445987 : ℝ) else
  if r = 15 then (4665056729501618734000/4705016532655031445987 : ℝ) else 1

def twentySevenCumulantExcess (r : ℕ) : ℝ :=
  (if r = 1 then (839/1161 : ℝ) else 0) +
  (if r = 3 then (33959/94041 : ℝ) else 0) +
  (if r = 4 then (7338037/22851963 : ℝ) else 0) +
  (if r = 5 then (163940999/617003001 : ℝ) else 0) +
  (if r = 6 then (132266999/617003001 : ℝ) else 0) +
  (if r = 7 then (76763184271/449795187729 : ℝ) else 0) +
  (if r = 8 then (1628864439317/12144470068683 : ℝ) else 0) +
  (if r = 9 then (33934746541559/327900691854441 : ℝ) else 0) +
  (if r = 10 then (76315007460677/983702075563323 : ℝ) else 0) +
  (if r = 11 then (4416146416628837/79679868120629163 : ℝ) else 0) +
  (if r = 12 then (233950380134271797/6454069317770962203 : ℝ) else 0) +
  (if r = 13 then (1132490030702304173/58086623859938659827 : ℝ) else 0) +
  (if r = 14 then (22127139144434506013/4705016532655031445987 : ℝ) else 0)

theorem twentySevenCumulantWeight_large {r : ℕ} (hr : 16 ≤ r) : twentySevenCumulantWeight r = 1 := by
  simp only [twentySevenCumulantWeight,
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
    ite_eq_right (show r ≠ 15 by omega)]

theorem twentySevenCumulantExcess_large {r : ℕ} (hr : 16 ≤ r) : twentySevenCumulantExcess r = 0 := by
  simp only [twentySevenCumulantExcess,
    ite_eq_right (show r ≠ 1 by omega),
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
    ite_eq_right (show r ≠ 14 by omega)]
  norm_num

theorem twentySevenCumulantWeight_pos (r : ℕ) : 0 < twentySevenCumulantWeight r := by
  unfold twentySevenCumulantWeight
  positivity

theorem twentySevenCumulantExcess_nonneg (r : ℕ) : 0 ≤ twentySevenCumulantExcess r := by
  unfold twentySevenCumulantExcess
  positivity

theorem twentySevenCumulantWeight_le_one_add_excess (r : ℕ) :
    twentySevenCumulantWeight r ≤ 1 + twentySevenCumulantExcess r := by
  by_cases hr : 16 ≤ r
  · rw [twentySevenCumulantWeight_large hr, twentySevenCumulantExcess_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentySevenCumulantWeight, twentySevenCumulantExcess]

theorem sum_twentySevenCumulantExcess_le (s : Finset ℕ) :
    (∑ j ∈ s, twentySevenCumulantExcess j) ≤ (5/2 : ℝ) := by
  have hterm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (∑ j ∈ s, if j = k then a else 0) ≤ a := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> simp_all
  simp only [twentySevenCumulantExcess, Finset.sum_add_distrib]
  linarith [
    hterm (839/1161 : ℝ) (by norm_num) 1,
    hterm (33959/94041 : ℝ) (by norm_num) 3,
    hterm (7338037/22851963 : ℝ) (by norm_num) 4,
    hterm (163940999/617003001 : ℝ) (by norm_num) 5,
    hterm (132266999/617003001 : ℝ) (by norm_num) 6,
    hterm (76763184271/449795187729 : ℝ) (by norm_num) 7,
    hterm (1628864439317/12144470068683 : ℝ) (by norm_num) 8,
    hterm (33934746541559/327900691854441 : ℝ) (by norm_num) 9,
    hterm (76315007460677/983702075563323 : ℝ) (by norm_num) 10,
    hterm (4416146416628837/79679868120629163 : ℝ) (by norm_num) 11,
    hterm (233950380134271797/6454069317770962203 : ℝ) (by norm_num) 12,
    hterm (1132490030702304173/58086623859938659827 : ℝ) (by norm_num) 13,
    hterm (22127139144434506013/4705016532655031445987 : ℝ) (by norm_num) 14]

def twentySevenIntegralWeight (r : ℕ) : ℝ :=
  if r = 1 then (1000/351 : ℝ) else
  if r = 2 then (7000/3159 : ℝ) else
  if r = 3 then (154000/85293 : ℝ) else
  if r = 4 then (10870750/6908733 : ℝ) else
  if r = 5 then (266078000/186535791 : ℝ) else
  if r = 6 then (6675342500/5036466357 : ℝ) else
  if r = 7 then (56748185875/45328197213 : ℝ) else
  if r = 8 then (1464011696375/1223861324751 : ℝ) else
  if r = 9 then (38085386449000/33044255768277 : ℝ) else
  if r = 10 then (76688683393000/68630377364883 : ℝ) else
  if r = 11 then (26221342497542750/24089262455073933 : ℝ) else
  if r = 12 then (2076632590841308625/1951230258860988573 : ℝ) else
  if r = 13 then (4229324507610287875/4052555153018976267 : ℝ) else
  if r = 14 then (486370726396387059250/474148952903220223239 : ℝ) else
  if r = 15 then (38796231381060880253500/38406065185160838082359 : ℝ) else 1

def twentySevenIntegralExcess (r : ℕ) : ℝ :=
  (if r = 1 then (649/351 : ℝ) else 0) +
  (if r = 2 then (3841/3159 : ℝ) else 0) +
  (if r = 3 then (68707/85293 : ℝ) else 0) +
  (if r = 4 then (3962017/6908733 : ℝ) else 0) +
  (if r = 5 then (79542209/186535791 : ℝ) else 0) +
  (if r = 6 then (1638876143/5036466357 : ℝ) else 0) +
  (if r = 7 then (11419988662/45328197213 : ℝ) else 0) +
  (if r = 8 then (240150371624/1223861324751 : ℝ) else 0) +
  (if r = 9 then (5041130680723/33044255768277 : ℝ) else 0) +
  (if r = 10 then (8058306028117/68630377364883 : ℝ) else 0) +
  (if r = 11 then (2132080042468817/24089262455073933 : ℝ) else 0) +
  (if r = 12 then (125402331980320052/1951230258860988573 : ℝ) else 0) +
  (if r = 13 then (176769354591311608/4052555153018976267 : ℝ) else 0) +
  (if r = 14 then (12221773493166836011/474148952903220223239 : ℝ) else 0) +
  (if r = 15 then (390166195900042171141/38406065185160838082359 : ℝ) else 0)

theorem twentySevenIntegralWeight_large {r : ℕ} (hr : 16 ≤ r) : twentySevenIntegralWeight r = 1 := by
  simp only [twentySevenIntegralWeight,
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
    ite_eq_right (show r ≠ 15 by omega)]

theorem twentySevenIntegralExcess_large {r : ℕ} (hr : 16 ≤ r) : twentySevenIntegralExcess r = 0 := by
  simp only [twentySevenIntegralExcess,
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
    ite_eq_right (show r ≠ 15 by omega)]
  norm_num

theorem twentySevenIntegralWeight_pos (r : ℕ) : 0 < twentySevenIntegralWeight r := by
  unfold twentySevenIntegralWeight
  positivity

theorem twentySevenIntegralExcess_nonneg (r : ℕ) : 0 ≤ twentySevenIntegralExcess r := by
  unfold twentySevenIntegralExcess
  positivity

theorem twentySevenIntegralWeight_le_one_add_excess (r : ℕ) :
    twentySevenIntegralWeight r ≤ 1 + twentySevenIntegralExcess r := by
  by_cases hr : 16 ≤ r
  · rw [twentySevenIntegralWeight_large hr, twentySevenIntegralExcess_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentySevenIntegralWeight, twentySevenIntegralExcess]

theorem sum_twentySevenIntegralExcess_le (s : Finset ℕ) :
    (∑ j ∈ s, twentySevenIntegralExcess j) ≤ (25/4 : ℝ) := by
  have hterm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (∑ j ∈ s, if j = k then a else 0) ≤ a := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> simp_all
  simp only [twentySevenIntegralExcess, Finset.sum_add_distrib]
  linarith [
    hterm (649/351 : ℝ) (by norm_num) 1,
    hterm (3841/3159 : ℝ) (by norm_num) 2,
    hterm (68707/85293 : ℝ) (by norm_num) 3,
    hterm (3962017/6908733 : ℝ) (by norm_num) 4,
    hterm (79542209/186535791 : ℝ) (by norm_num) 5,
    hterm (1638876143/5036466357 : ℝ) (by norm_num) 6,
    hterm (11419988662/45328197213 : ℝ) (by norm_num) 7,
    hterm (240150371624/1223861324751 : ℝ) (by norm_num) 8,
    hterm (5041130680723/33044255768277 : ℝ) (by norm_num) 9,
    hterm (8058306028117/68630377364883 : ℝ) (by norm_num) 10,
    hterm (2132080042468817/24089262455073933 : ℝ) (by norm_num) 11,
    hterm (125402331980320052/1951230258860988573 : ℝ) (by norm_num) 12,
    hterm (176769354591311608/4052555153018976267 : ℝ) (by norm_num) 13,
    hterm (12221773493166836011/474148952903220223239 : ℝ) (by norm_num) 14,
    hterm (390166195900042171141/38406065185160838082359 : ℝ) (by norm_num) 15]

def twentySevenRankConvolution (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (r-2), twentySevenIntegralWeight j * twentySevenCumulantWeight (r-j)

theorem twentySevenRankConvolution_nonneg (r : ℕ) : 0 ≤ twentySevenRankConvolution r := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (twentySevenIntegralWeight_pos j).le
    (twentySevenCumulantWeight_pos (r-j)).le

end KLS
end
