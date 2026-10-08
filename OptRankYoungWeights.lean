import KLS.CumulantFactorialMajorant

/-! Rational finite-rank envelopes with separate Young parameters. -/
open scoped BigOperators
set_option maxHeartbeats 4000000
noncomputable section
namespace KLS

def rankYoungCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then 1 else
  if r = 2 then 2 else
  if r = 3 then (11411/20 : ℝ) else
  if r = 4 then (744531/50 : ℝ) else
  if r = 5 then (7696247/20 : ℝ) else
  if r = 6 then (199255251/20 : ℝ) else
  if r = 7 then (6478106767/25 : ℝ) else
  if r = 8 then (338544323193/50 : ℝ) else
  if r = 9 then (17763782131477/100 : ℝ) else
  if r = 10 then (233809587986617/50 : ℝ) else
  if r = 11 then (12344166668054699/100 : ℝ) else
  if r = 12 then (326611468989319107/100 : ℝ) else
  if r = 13 then (4329122230751097919/50 : ℝ) else
  if r = 14 then (57472100683090134802/25 : ℝ) else
  if r = 15 then (6111959386305175684023/100 : ℝ) else
  if r = 16 then (162677761317981112887273/100 : ℝ) else 2

@[simp] theorem rankYoungCumulantWeight_1 : rankYoungCumulantWeight 1 = 1 := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_2 : rankYoungCumulantWeight 2 = 2 := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_3 : rankYoungCumulantWeight 3 = (11411/20 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_4 : rankYoungCumulantWeight 4 = (744531/50 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_5 : rankYoungCumulantWeight 5 = (7696247/20 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_6 : rankYoungCumulantWeight 6 = (199255251/20 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_7 : rankYoungCumulantWeight 7 = (6478106767/25 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_8 : rankYoungCumulantWeight 8 = (338544323193/50 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_9 : rankYoungCumulantWeight 9 = (17763782131477/100 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_10 : rankYoungCumulantWeight 10 = (233809587986617/50 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_11 : rankYoungCumulantWeight 11 = (12344166668054699/100 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_12 : rankYoungCumulantWeight 12 = (326611468989319107/100 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_13 : rankYoungCumulantWeight 13 = (4329122230751097919/50 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_14 : rankYoungCumulantWeight 14 = (57472100683090134802/25 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_15 : rankYoungCumulantWeight 15 = (6111959386305175684023/100 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

@[simp] theorem rankYoungCumulantWeight_16 : rankYoungCumulantWeight 16 = (162677761317981112887273/100 : ℝ) := by
  norm_num [rankYoungCumulantWeight]

theorem rankYoungCumulantWeight_nonneg (r : ℕ) : 0 ≤ rankYoungCumulantWeight r := by
  unfold rankYoungCumulantWeight
  positivity

def rankYoungIntegralWeight (r : ℕ) : ℝ :=
  if r = 1 then 8 else
  if r = 2 then (16639/100 : ℝ) else
  if r = 3 then (182231/50 : ℝ) else
  if r = 4 then (8572083/100 : ℝ) else
  if r = 5 then (104899317/50 : ℝ) else
  if r = 6 then (2630444873/50 : ℝ) else
  if r = 7 then (134047387643/100 : ℝ) else
  if r = 8 then (863423190648/25 : ℝ) else
  if r = 9 then (44850785215359/50 : ℝ) else
  if r = 10 then (2343798781278339/100 : ℝ) else
  if r = 11 then (61522040708127169/100 : ℝ) else
  if r = 12 then (405165421407165916/25 : ℝ) else
  if r = 13 then (42813788584139889219/100 : ℝ) else
  if r = 14 then (566804323528847687081/50 : ℝ) else
  if r = 15 then (1503545023441412699127/5 : ℝ) else
  if r = 16 then (199723998836752383334727/25 : ℝ) else 2

@[simp] theorem rankYoungIntegralWeight_1 : rankYoungIntegralWeight 1 = 8 := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_2 : rankYoungIntegralWeight 2 = (16639/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_3 : rankYoungIntegralWeight 3 = (182231/50 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_4 : rankYoungIntegralWeight 4 = (8572083/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_5 : rankYoungIntegralWeight 5 = (104899317/50 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_6 : rankYoungIntegralWeight 6 = (2630444873/50 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_7 : rankYoungIntegralWeight 7 = (134047387643/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_8 : rankYoungIntegralWeight 8 = (863423190648/25 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_9 : rankYoungIntegralWeight 9 = (44850785215359/50 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_10 : rankYoungIntegralWeight 10 = (2343798781278339/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_11 : rankYoungIntegralWeight 11 = (61522040708127169/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_12 : rankYoungIntegralWeight 12 = (405165421407165916/25 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_13 : rankYoungIntegralWeight 13 = (42813788584139889219/100 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_14 : rankYoungIntegralWeight 14 = (566804323528847687081/50 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_15 : rankYoungIntegralWeight 15 = (1503545023441412699127/5 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

@[simp] theorem rankYoungIntegralWeight_16 : rankYoungIntegralWeight 16 = (199723998836752383334727/25 : ℝ) := by
  norm_num [rankYoungIntegralWeight]

theorem rankYoungIntegralWeight_nonneg (r : ℕ) : 0 ≤ rankYoungIntegralWeight r := by
  unfold rankYoungIntegralWeight
  positivity

def rankYoungRootAllowance (r : ℕ) : ℝ :=
  if r = 1 then 0 else
  if r = 2 then 0 else
  if r = 3 then (258/5 : ℝ) else
  if r = 4 then (129501/25 : ℝ) else
  if r = 5 then (21625963/100 : ℝ) else
  if r = 6 then (187744167/25 : ℝ) else
  if r = 7 then (4836163447/20 : ℝ) else
  if r = 8 then (149582308253/20 : ℝ) else
  if r = 9 then (22567345368589/100 : ℝ) else
  if r = 10 then (334823334927407/50 : ℝ) else
  if r = 11 then (19631969041615041/100 : ℝ) else
  if r = 12 then (570296061277376073/100 : ℝ) else
  if r = 13 then (8223855709176057987/50 : ℝ) else
  if r = 14 then (117898823472701679516/25 : ℝ) else
  if r = 15 then (3364068761585163277068/25 : ℝ) else
  if r = 16 then (382380194965285390756801/100 : ℝ) else 2

@[simp] theorem rankYoungRootAllowance_1 : rankYoungRootAllowance 1 = 0 := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_2 : rankYoungRootAllowance 2 = 0 := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_3 : rankYoungRootAllowance 3 = (258/5 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_4 : rankYoungRootAllowance 4 = (129501/25 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_5 : rankYoungRootAllowance 5 = (21625963/100 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_6 : rankYoungRootAllowance 6 = (187744167/25 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_7 : rankYoungRootAllowance 7 = (4836163447/20 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_8 : rankYoungRootAllowance 8 = (149582308253/20 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_9 : rankYoungRootAllowance 9 = (22567345368589/100 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_10 : rankYoungRootAllowance 10 = (334823334927407/50 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_11 : rankYoungRootAllowance 11 = (19631969041615041/100 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_12 : rankYoungRootAllowance 12 = (570296061277376073/100 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_13 : rankYoungRootAllowance 13 = (8223855709176057987/50 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_14 : rankYoungRootAllowance 14 = (117898823472701679516/25 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_15 : rankYoungRootAllowance 15 = (3364068761585163277068/25 : ℝ) := by
  norm_num [rankYoungRootAllowance]

@[simp] theorem rankYoungRootAllowance_16 : rankYoungRootAllowance 16 = (382380194965285390756801/100 : ℝ) := by
  norm_num [rankYoungRootAllowance]

theorem rankYoungRootAllowance_nonneg (r : ℕ) : 0 ≤ rankYoungRootAllowance r := by
  unfold rankYoungRootAllowance
  positivity

def rankYoungParameter (r : ℕ) : ℝ :=
  if r = 1 then 2 else
  if r = 2 then (4031/2500 : ℝ) else
  if r = 3 then (16547/10000 : ℝ) else
  if r = 4 then (17147/10000 : ℝ) else
  if r = 5 then (17491/10000 : ℝ) else
  if r = 6 then (3541/2000 : ℝ) else
  if r = 7 then (17847/10000 : ℝ) else
  if r = 8 then (17947/10000 : ℝ) else
  if r = 9 then (18019/10000 : ℝ) else
  if r = 10 then (18073/10000 : ℝ) else
  if r = 11 then (9057/5000 : ℝ) else
  if r = 12 then (18147/10000 : ℝ) else
  if r = 13 then (4543/2500 : ℝ) else
  if r = 14 then (18193/10000 : ℝ) else
  if r = 15 then (1821/1000 : ℝ) else
  if r = 16 then (1139/625 : ℝ) else 2

@[simp] theorem rankYoungParameter_1 : rankYoungParameter 1 = 2 := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_2 : rankYoungParameter 2 = (4031/2500 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_3 : rankYoungParameter 3 = (16547/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_4 : rankYoungParameter 4 = (17147/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_5 : rankYoungParameter 5 = (17491/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_6 : rankYoungParameter 6 = (3541/2000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_7 : rankYoungParameter 7 = (17847/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_8 : rankYoungParameter 8 = (17947/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_9 : rankYoungParameter 9 = (18019/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_10 : rankYoungParameter 10 = (18073/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_11 : rankYoungParameter 11 = (9057/5000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_12 : rankYoungParameter 12 = (18147/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_13 : rankYoungParameter 13 = (4543/2500 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_14 : rankYoungParameter 14 = (18193/10000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_15 : rankYoungParameter 15 = (1821/1000 : ℝ) := by
  norm_num [rankYoungParameter]

@[simp] theorem rankYoungParameter_16 : rankYoungParameter 16 = (1139/625 : ℝ) := by
  norm_num [rankYoungParameter]

theorem rankYoungParameter_nonneg (r : ℕ) : 0 ≤ rankYoungParameter r := by
  unfold rankYoungParameter
  positivity

theorem rankYoungParameter_one_lt (r : ℕ) : 1 < rankYoungParameter r := by
  by_cases hr : r ≤ 16
  · interval_cases r <;> norm_num [rankYoungParameter]
  · have h1 : r ≠ 1 := by omega
    have h2 : r ≠ 2 := by omega
    have h3 : r ≠ 3 := by omega
    have h4 : r ≠ 4 := by omega
    have h5 : r ≠ 5 := by omega
    have h6 : r ≠ 6 := by omega
    have h7 : r ≠ 7 := by omega
    have h8 : r ≠ 8 := by omega
    have h9 : r ≠ 9 := by omega
    have h10 : r ≠ 10 := by omega
    have h11 : r ≠ 11 := by omega
    have h12 : r ≠ 12 := by omega
    have h13 : r ≠ 13 := by omega
    have h14 : r ≠ 14 := by omega
    have h15 : r ≠ 15 := by omega
    have h16 : r ≠ 16 := by omega
    simp [rankYoungParameter, *]

def rankYoungCoercivity (r : ℕ) : ℝ := 1-(rankYoungParameter r)⁻¹

theorem rankYoungCoercivity_pos (r : ℕ) : 0 < rankYoungCoercivity r := by
  have h := rankYoungParameter_one_lt r
  exact sub_pos.mpr ((inv_lt_one₀ (by linarith : 0 < rankYoungParameter r)).mpr h)

def rankYoungCauchyWeight (r j : ℕ) : ℝ :=
  if r = 3 then if j = 1 then 256 else 1 else
  if r = 4 then if j = 1 then 256 else if j = 2 then 70 else 1 else
  if r = 5 then if j = 1 then 256 else if j = 2 then 229 else if j = 3 then 64 else 1 else
  if r = 6 then if j = 1 then 256 else if j = 2 then 230 else if j = 3 then 211 else if j = 4 then 61 else 1 else
  if r = 7 then if j = 1 then 256 else if j = 2 then 230 else if j = 3 then 212 else if j = 4 then 201 else if j = 5 then 59 else 1 else
  if r = 8 then if j = 1 then 256 else if j = 2 then 229 else if j = 3 then 211 else if j = 4 then 201 else if j = 5 then 195 else if j = 6 then 58 else 1 else
  if r = 9 then if j = 1 then 256 else if j = 2 then 229 else if j = 3 then 210 else if j = 4 then 200 else if j = 5 then 195 else if j = 6 then 191 else if j = 7 then 57 else 1 else
  if r = 10 then if j = 1 then 256 else if j = 2 then 228 else if j = 3 then 209 else if j = 4 then 199 else if j = 5 then 193 else if j = 6 then 191 else if j = 7 then 188 else if j = 8 then 57 else 1 else
  if r = 11 then if j = 1 then 256 else if j = 2 then 228 else if j = 3 then 208 else if j = 4 then 198 else if j = 5 then 192 else if j = 6 then 189 else if j = 7 then 187 else if j = 8 then 186 else if j = 9 then 57 else 1 else
  if r = 12 then if j = 1 then 256 else if j = 2 then 228 else if j = 3 then 208 else if j = 4 then 197 else if j = 5 then 190 else if j = 6 then 187 else if j = 7 then 186 else if j = 8 then 185 else if j = 9 then 185 else if j = 10 then 56 else 1 else
  if r = 13 then if j = 1 then 256 else if j = 2 then 227 else if j = 3 then 207 else if j = 4 then 196 else if j = 5 then 189 else if j = 6 then 185 else if j = 7 then 184 else if j = 8 then 183 else if j = 9 then 184 else if j = 10 then 184 else if j = 11 then 56 else 1 else
  if r = 14 then if j = 1 then 256 else if j = 2 then 227 else if j = 3 then 207 else if j = 4 then 195 else if j = 5 then 188 else if j = 6 then 184 else if j = 7 then 182 else if j = 8 then 181 else if j = 9 then 181 else if j = 10 then 182 else if j = 11 then 183 else if j = 12 then 56 else 1 else
  if r = 15 then if j = 1 then 256 else if j = 2 then 227 else if j = 3 then 206 else if j = 4 then 195 else if j = 5 then 187 else if j = 6 then 183 else if j = 7 then 180 else if j = 8 then 179 else if j = 9 then 179 else if j = 10 then 180 else if j = 11 then 181 else if j = 12 then 182 else if j = 13 then 56 else 1 else
  if r = 16 then if j = 1 then 256 else if j = 2 then 227 else if j = 3 then 206 else if j = 4 then 194 else if j = 5 then 187 else if j = 6 then 182 else if j = 7 then 179 else if j = 8 then 178 else if j = 9 then 177 else if j = 10 then 177 else if j = 11 then 179 else if j = 12 then 180 else if j = 13 then 181 else if j = 14 then 56 else 1 else
  1

theorem rankYoungCauchyWeight_pos (r j : ℕ) : 0 < rankYoungCauchyWeight r j := by
  unfold rankYoungCauchyWeight
  positivity

def rankYoungConvolution (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (r-2), rankYoungCauchyWeight r j) *
  (∑ j ∈ Finset.Icc 1 (r-2), rankYoungIntegralWeight j*rankYoungCumulantWeight (r-j)/rankYoungCauchyWeight r j)

theorem rankYoungConvolution_nonneg (r : ℕ) : 0 ≤ rankYoungConvolution r := by
  apply mul_nonneg
  · exact Finset.sum_nonneg fun j _ => (rankYoungCauchyWeight_pos r j).le
  · exact Finset.sum_nonneg fun j _ => div_nonneg
      (mul_nonneg (rankYoungIntegralWeight_nonneg j) (rankYoungCumulantWeight_nonneg (r-j)))
      (rankYoungCauchyWeight_pos r j).le

end KLS
end
