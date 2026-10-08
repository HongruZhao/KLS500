import KLS.CumulantFactorialMajorant

/-! Five rational initial envelopes and the exact finite cardinality sum
used to control their contribution to the lower-tensor convolution. -/
open scoped BigOperators
noncomputable section
namespace KLS

def thirtyRankWeight (r : ℕ) : ℝ :=
  if r = 1 then 2 else if r = 2 then 22/15 else if r = 3 then 5/4 else
    if r = 4 then 9/8 else if r = 5 then 21/20 else 1

def thirtyRankConvolution (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (r-2), thirtyRankWeight j * thirtyRankWeight (r-j)

theorem thirtyRankWeight_pos (r : ℕ) : 0 < thirtyRankWeight r := by
  unfold thirtyRankWeight
  split_ifs <;> norm_num

theorem thirtyRankWeight_one_le (r : ℕ) : 1 ≤ thirtyRankWeight r := by
  unfold thirtyRankWeight
  split_ifs <;> norm_num

theorem thirtyRankWeight_eq_one {r : ℕ} (hr : 6 ≤ r) : thirtyRankWeight r = 1 := by
  have h1 : r ≠ 1 := by omega
  have h2 : r ≠ 2 := by omega
  have h3 : r ≠ 3 := by omega
  have h4 : r ≠ 4 := by omega
  have h5 : r ≠ 5 := by omega
  simp [thirtyRankWeight, h1, h2, h3, h4, h5]

theorem thirtyRankWeight_excess_eq (r : ℕ) :
    thirtyRankWeight r - 1 = (if r = 1 then 1 else 0) +
      (if r = 2 then (7/15 : ℝ) else 0) + (if r = 3 then (1/4 : ℝ) else 0) +
      (if r = 4 then (1/8 : ℝ) else 0) + (if r = 5 then (1/20 : ℝ) else 0) := by
  unfold thirtyRankWeight
  split_ifs <;> norm_num [*] at *

theorem sum_thirtyRankWeight_excess_le_two (s : Finset ℕ) :
    (∑ j ∈ s, (thirtyRankWeight j - 1)) ≤ 2 := by
  simp only [thirtyRankWeight_excess_eq, Finset.sum_add_distrib, Finset.sum_ite_eq']
  split_ifs <;> norm_num

theorem sum_subsetBinomialWeight_mul_card {r : ℕ} (F : ℕ → ℝ) :
    (∑ T ∈ activeTailSubsets r, subsetBinomialWeight T * F T.card) =
      ∑ j ∈ Finset.Icc 1 (r-2), F j := by
  have hmap (T : Finset (Fin r)) (hT : T ∈ activeTailSubsets r) :
      T.card ∈ Finset.Icc 1 (r-2) := by simpa using hT
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro j hj
  have hf : (activeTailSubsets r).filter (fun T => T.card = j) =
      (Finset.univ : Finset (Fin r)).powersetCard j := by
    ext T
    simp only [Finset.mem_filter, mem_activeTailSubsets, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by simpa [h] using hj, h⟩
  rw [hf]
  have he (T : Finset (Fin r)) (hT : T ∈ Finset.univ.powersetCard j) :
      subsetBinomialWeight T * F T.card = (r.choose j : ℝ)⁻¹ * F j := by
    rw [subsetBinomialWeight, (Finset.mem_powersetCard.mp hT).2]
  rw [Finset.sum_congr rfl he, Finset.sum_const, Finset.card_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀]
  · simp
  · exact_mod_cast (Nat.choose_pos (by have := Finset.mem_Icc.mp hj; omega)).ne'

theorem thirtyRankConvolution_nonneg (r : ℕ) : 0 ≤ thirtyRankConvolution r := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (thirtyRankWeight_pos j).le
    (thirtyRankWeight_pos (r-j)).le

theorem thirtyRankConvolution_bound {r : ℕ} (hr : 7 ≤ r) :
    ((r-2 : ℕ) : ℝ) * thirtyRankConvolution r ≤ (r : ℝ)^2 := by
  by_cases hlarge : 11 ≤ r
  · have hprod (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
        thirtyRankWeight j * thirtyRankWeight (r-j) =
          1 + (thirtyRankWeight j - 1) + (thirtyRankWeight (r-j) - 1) := by
      have hj' := Finset.mem_Icc.mp hj
      by_cases hjs : 6 ≤ j
      · rw [thirtyRankWeight_eq_one hjs]
        ring
      · have hcomp : 6 ≤ r-j := by omega
        rw [thirtyRankWeight_eq_one hcomp]
        ring
    have hfirst := sum_thirtyRankWeight_excess_le_two (Finset.Icc 1 (r-2))
    have hsecond : (∑ j ∈ Finset.Icc 1 (r-2), (thirtyRankWeight (r-j) - 1)) ≤ 2 := by
      have hinj : Set.InjOn (fun j : ℕ => r-j) (↑(Finset.Icc 1 (r-2)) : Set ℕ) := by
        intro a ha b hb he
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        change r-a = r-b at he
        omega
      rw [← Finset.sum_image (g := fun j : ℕ => r-j) (f := fun j => thirtyRankWeight j - 1) hinj]
      exact sum_thirtyRankWeight_excess_le_two _
    have hsum : thirtyRankConvolution r ≤ ((r-2 : ℕ) : ℝ) + 4 := by
      unfold thirtyRankConvolution
      rw [Finset.sum_congr rfl hprod]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at ⊢
      have hcard : (Finset.Icc 1 (r-2)).card = r-2 := by simp
      rw [hcard]
      linarith
    have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) (r-2))
    rw [Nat.cast_sub (by omega : 2 ≤ r)] at hm ⊢
    norm_num only [Nat.cast_ofNat] at hm ⊢
    nlinarith
  · interval_cases r <;> norm_num [thirtyRankConvolution, thirtyRankWeight,
      Finset.sum_Icc_succ_top]

end KLS
end
