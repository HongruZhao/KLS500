import IteratedResolventNumerics

noncomputable section
namespace KLS.ConstantReduction

theorem refined_iterated_resolvent_contraction_certificate :
    (51842/51843 : ℝ)^65536 ≤ 283/1000 := by
  have hblock : (51842/51843 : ℝ)^256 ≤ 99508/100000 := by norm_num
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (51842/51843 : ℝ)^256) hblock 256
  rw [← pow_mul] at hh
  exact hh.trans (by norm_num)

theorem refined_iterated_resolvent_displacement_certificate {C : ℝ} (hC : 0 < C) :
    Real.sqrt (2*(C/51842))*(1+Real.sqrt ((65534:ℝ)+1)) ≤
      (257/161)*Real.sqrt C := by
  have hroot : Real.sqrt (2*(C/51842)) = Real.sqrt C/161 := by
    rw [show 2*(C/51842) = C/(161^2) by ring, Real.sqrt_div hC.le,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 161)]
  have hbound : Real.sqrt ((65534:ℝ)+1) ≤ 256 := by
    have hh := Real.sqrt_le_sqrt (by norm_num : (65534:ℝ)+1 ≤ 65536)
    norm_num at hh ⊢
    exact hh
  rw [hroot]
  calc
    _ ≤ (Real.sqrt C/161)*(1+256) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) (by positivity)
    _ = _ := by ring

end KLS.ConstantReduction
end
