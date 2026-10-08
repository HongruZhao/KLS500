import OptRankSymmetric256Weights

/-! Pure numerical coefficients. Actual Taylor discharge is a separate module. -/
noncomputable section
namespace KLS.ConstantReduction

def moving256RankTaylorCoefficient (d : ℕ) : ℝ :=
  if d ≤ 256 then rankSymmetric256CumulantWeight d else (63/500)*(91/5)^d

theorem moving256RankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ moving256RankTaylorCoefficient d := by
  have hh := rankSymmetric256CumulantWeight_nonneg d
  unfold moving256RankTaylorCoefficient
  split_ifs <;> positivity

theorem moving256RankTaylorCoefficient_large {d : ℕ} (hd : 257 ≤ d) :
    moving256RankTaylorCoefficient d = (63/500 : ℝ)*(91/5 : ℝ)^d := by
  simp only [moving256RankTaylorCoefficient, show ¬d ≤ 256 by omega, ↓reduceIte]

end KLS.ConstantReduction
end
