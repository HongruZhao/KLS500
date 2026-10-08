import OptRankWeights

/-! Explicit rational envelopes for ranks one through twenty-five.  Their
finite coefficient and square inequalities are checked in Lean. -/
open scoped BigOperators
set_option maxHeartbeats 1000000
noncomputable section
namespace KLS

def twentyNineRankWeight (r : ℕ) : ℝ :=
    if r = 1 then (480/203 : ℝ) else
    if r = 2 then (6849/4000 : ℝ) else
    if r = 3 then (144059/100000 : ℝ) else
    if r = 4 then (129367/100000 : ℝ) else
    if r = 5 then (6013/5000 : ℝ) else
    if r = 6 then (114119/100000 : ℝ) else
    if r = 7 then (27433/25000 : ℝ) else
    if r = 8 then (106461/100000 : ℝ) else
    if r = 9 then (5197/5000 : ℝ) else
    if r = 10 then (101943/100000 : ℝ) else
    if r = 11 then (4013/4000 : ℝ) else
    if r = 12 then (98987/100000 : ℝ) else
    if r = 13 then (97861/100000 : ℝ) else
    if r = 14 then (48449/50000 : ℝ) else
    if r = 15 then (48031/50000 : ℝ) else
    if r = 16 then (47663/50000 : ℝ) else
    if r = 17 then (94669/100000 : ℝ) else
    if r = 18 then (23519/25000 : ℝ) else
    if r = 19 then (18707/20000 : ℝ) else
    if r = 20 then (93037/100000 : ℝ) else
    if r = 21 then (46287/50000 : ℝ) else
    if r = 22 then (92139/100000 : ℝ) else
    if r = 23 then (5733/6250 : ℝ) else
    if r = 24 then (91337/100000 : ℝ) else
    if r = 25 then (90963/100000 : ℝ) else 1

def twentyNinePositiveExcess (r : ℕ) : ℝ :=
    (if r = 1 then (277/203 : ℝ) else 0) +
    (if r = 2 then (2849/4000 : ℝ) else 0) +
    (if r = 3 then (44059/100000 : ℝ) else 0) +
    (if r = 4 then (29367/100000 : ℝ) else 0) +
    (if r = 5 then (1013/5000 : ℝ) else 0) +
    (if r = 6 then (14119/100000 : ℝ) else 0) +
    (if r = 7 then (2433/25000 : ℝ) else 0) +
    (if r = 8 then (6461/100000 : ℝ) else 0) +
    (if r = 9 then (197/5000 : ℝ) else 0) +
    (if r = 10 then (1943/100000 : ℝ) else 0) +
    (if r = 11 then (13/4000 : ℝ) else 0)

def twentyNineRankConvolution (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (r-2), twentyNineRankWeight j * twentyNineRankWeight (r-j)

def twentyNineRootAllowance (r : ℕ) : ℝ :=
    if r = 2 then 0 else
    if r = 3 then (36989/5000 : ℝ) else
    if r = 4 then (30017/2500 : ℝ) else
    if r = 5 then (156483/10000 : ℝ) else
    if r = 6 then (23553/1250 : ℝ) else
    if r = 7 then (13621/625 : ℝ) else
    if r = 8 then (245981/10000 : ℝ) else
    if r = 9 then (273069/10000 : ℝ) else
    if r = 10 then (74873/2500 : ℝ) else
    if r = 11 then (162713/5000 : ℝ) else
    if r = 12 then (43873/1250 : ℝ) else
    if r = 13 then (376239/10000 : ℝ) else
    if r = 14 then (10031/250 : ℝ) else
    if r = 15 then (213011/5000 : ℝ) else
    if r = 16 then (450607/10000 : ℝ) else
    if r = 17 then (47501/1000 : ℝ) else
    if r = 18 then (499241/10000 : ℝ) else
    if r = 19 then (130827/2500 : ℝ) else
    if r = 20 then (273609/5000 : ℝ) else
    if r = 21 then (35686/625 : ℝ) else
    if r = 22 then (594583/10000 : ℝ) else
    if r = 23 then (309019/5000 : ℝ) else
    if r = 24 then (128269/2000 : ℝ) else
    if r = 25 then (83063/1250 : ℝ) else (45/16 : ℝ) * ((r : ℝ)+7/5)

theorem twentyNineRankWeight_large {r : ℕ} (hr : 26 ≤ r) : twentyNineRankWeight r = 1 := by
  simp only [twentyNineRankWeight,
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
    ite_eq_right (show r ≠ 25 by omega)]

theorem twentyNineRankWeight_pos (r : ℕ) : 0 < twentyNineRankWeight r := by
  by_cases hr : 26 ≤ r
  · rw [twentyNineRankWeight_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentyNineRankWeight]

theorem twentyNineRankWeight_le_three (r : ℕ) : twentyNineRankWeight r ≤ 3 := by
  by_cases hr : 26 ≤ r
  · rw [twentyNineRankWeight_large hr]
    norm_num
  · interval_cases r <;> norm_num [twentyNineRankWeight]

theorem twentyNineRankWeight_le_one {r : ℕ} (hr : 12 ≤ r) : twentyNineRankWeight r ≤ 1 := by
  by_cases hlarge : 26 ≤ r
  · rw [twentyNineRankWeight_large hlarge]
  · interval_cases r <;> norm_num [twentyNineRankWeight]

theorem twentyNinePositiveExcess_nonneg (r : ℕ) : 0 ≤ twentyNinePositiveExcess r := by
  unfold twentyNinePositiveExcess
  positivity

theorem twentyNinePositiveExcess_large {r : ℕ} (hr : 12 ≤ r) : twentyNinePositiveExcess r = 0 := by
  simp only [twentyNinePositiveExcess,
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
    ite_eq_right (show r ≠ 11 by omega)]
  norm_num

theorem twentyNineRankWeight_le_one_add_excess (r : ℕ) :
    twentyNineRankWeight r ≤ 1 + twentyNinePositiveExcess r := by
  by_cases hr : 26 ≤ r
  · rw [twentyNineRankWeight_large hr, twentyNinePositiveExcess_large (by omega : 12 ≤ r)]
    norm_num
  · interval_cases r <;> norm_num [twentyNineRankWeight, twentyNinePositiveExcess]

theorem sum_twentyNinePositiveExcess_le (s : Finset ℕ) :
    (∑ j ∈ s, twentyNinePositiveExcess j) ≤ (17/5 : ℝ) := by
  have hterm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : (∑ j ∈ s, if j = k then a else 0) ≤ a := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> simp_all
  simp only [twentyNinePositiveExcess, Finset.sum_add_distrib]
  linarith [
    hterm (277/203 : ℝ) (by norm_num) 1,
    hterm (2849/4000 : ℝ) (by norm_num) 2,
    hterm (44059/100000 : ℝ) (by norm_num) 3,
    hterm (29367/100000 : ℝ) (by norm_num) 4,
    hterm (1013/5000 : ℝ) (by norm_num) 5,
    hterm (14119/100000 : ℝ) (by norm_num) 6,
    hterm (2433/25000 : ℝ) (by norm_num) 7,
    hterm (6461/100000 : ℝ) (by norm_num) 8,
    hterm (197/5000 : ℝ) (by norm_num) 9,
    hterm (1943/100000 : ℝ) (by norm_num) 10,
    hterm (13/4000 : ℝ) (by norm_num) 11]

theorem twentyNineRankConvolution_nonneg (r : ℕ) : 0 ≤ twentyNineRankConvolution r := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (twentyNineRankWeight_pos j).le
    (twentyNineRankWeight_pos (r-j)).le

theorem twentyNineRankConvolution_bound {r : ℕ} (hr : 26 ≤ r) :
    ((r-2 : ℕ) : ℝ) * twentyNineRankConvolution r ≤ ((r : ℝ)+7/5)^2 := by
  have hprod (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
      twentyNineRankWeight j * twentyNineRankWeight (r-j) ≤
        1 + twentyNinePositiveExcess j + twentyNinePositiveExcess (r-j) := by
    have hj' := Finset.mem_Icc.mp hj
    have hmul := mul_le_mul (twentyNineRankWeight_le_one_add_excess j)
      (twentyNineRankWeight_le_one_add_excess (r-j)) (twentyNineRankWeight_pos _).le
      (show 0 ≤ 1 + twentyNinePositiveExcess j by have := twentyNinePositiveExcess_nonneg j; linarith)
    apply hmul.trans_eq
    by_cases hjs : 12 ≤ j
    · rw [twentyNinePositiveExcess_large hjs]
      ring
    · have hcomp : 12 ≤ r-j := by omega
      rw [twentyNinePositiveExcess_large hcomp]
      ring
  have hfirst := sum_twentyNinePositiveExcess_le (Finset.Icc 1 (r-2))
  have hsecond : (∑ j ∈ Finset.Icc 1 (r-2), twentyNinePositiveExcess (r-j)) ≤ (17/5 : ℝ) := by
    have hinj : Set.InjOn (fun j : ℕ => r-j) (↑(Finset.Icc 1 (r-2)) : Set ℕ) := by
      intro a ha b hb he
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      change r-a = r-b at he
      omega
    rw [← Finset.sum_image (g := fun j : ℕ => r-j) (f := twentyNinePositiveExcess) hinj]
    exact sum_twentyNinePositiveExcess_le _
  have hsum : twentyNineRankConvolution r ≤ ((r-2 : ℕ) : ℝ) + 34/5 := by
    unfold twentyNineRankConvolution
    have hh := Finset.sum_le_sum hprod
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    have hcard : (Finset.Icc 1 (r-2)).card = r-2 := by simp
    rw [hcard] at hh
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) (r-2))
  rw [Nat.cast_sub (by omega : 2 ≤ r)] at hm ⊢
  norm_num only [Nat.cast_ofNat] at hm ⊢
  nlinarith

theorem twentyNineRootAllowance_large {r : ℕ} (hr : 26 ≤ r) :
    twentyNineRootAllowance r = (45/16 : ℝ) * ((r : ℝ)+7/5) := by
  simp only [twentyNineRootAllowance,
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
    ite_eq_right (show r ≠ 25 by omega)]

theorem twentyNineRootAllowance_nonneg (r : ℕ) : 0 ≤ twentyNineRootAllowance r := by
  by_cases hr : 26 ≤ r
  · rw [twentyNineRootAllowance_large hr]
    positivity
  · interval_cases r <;> norm_num [twentyNineRootAllowance]

end KLS
end
