import KLS.WeightedResolventVariance

noncomputable section
namespace KLS.ConstantReduction

/-- The entropy supersolution quadratic propagates the mixed coefficient. -/
theorem entropy_mixed_quadratic_step {H G a b s : ℝ}
    (hH : 0 < H) (hG : 0 ≤ G) (_ha : 0 ≤ a) (hs : 0 < s)
    (hb : a ≤ b) (heq : b^2-a*b=s)
    (hbound : a*G+s*G^2/H ≤ H) : b*G ≤ H := by
  have hquad : a*G*H+s*G^2 ≤ H^2 := by
    have hh := mul_le_mul_of_nonneg_right hbound hH.le
    field_simp at hh
    nlinarith only [hh]
  have haG : a*G ≤ H := by
    have hn : 0 ≤ s*G^2/H := by positivity
    linarith
  by_contra hnot
  have hlt : H < b*G := lt_of_not_ge hnot
  have hpos : 0 < H+b*G-a*G := by
    have hbg : a*G ≤ b*G := mul_le_mul_of_nonneg_right hb hG
    linarith
  have hm := mul_pos (sub_pos.mpr hlt) hpos
  have hscaled := congrArg (fun z : ℝ => z*G^2) heq
  nlinarith only [hquad,hm,hscaled]

end KLS.ConstantReduction
end
