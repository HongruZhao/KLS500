import OptVarianceODE
import OptVarianceAffine
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The sharp scalar third-moment differential inequality follows from
global positive variance and the quadratic-variance differential inequality. -/
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

theorem varianceODE_deriv_sq_le {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hpos : ∀ t, 0<v t)
    (hsecond : ∀ t, deriv (deriv v) t≤6*(v t)^2) (t₀ : ℝ) :
    (deriv v t₀)^2≤4*(v t₀)^3 := by
  by_cases hz : deriv v t₀=0
  · rw [hz,zero_pow (by norm_num : 2≠0)]
    have hp := hpos t₀
    positivity
  let b : ℝ := if deriv v t₀<0 then 1 else -1
  have hb : b^2=1 := by dsimp [b]; split_ifs <;> norm_num
  have hbneg : deriv v t₀*b<0 := by
    dsimp [b]
    split_ifs with hn
    · simpa using hn
    · have hp : 0<deriv v t₀ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      nlinarith
  let w : ℝ → ℝ := fun s => v (t₀+b*s)
  have hw : ContDiff ℝ 2 w := hv.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hwpos : ∀ t, 0<w t := fun t => hpos (t₀+b*t)
  have hwsecond : ∀ t, deriv (deriv w) t≤6*(w t)^2 := by
    intro t
    dsimp only [w]
    rw [secondDeriv_comp_affine hv t₀ b t,hb,one_mul]
    exact hsecond _
  have hwneg : deriv w 0<0 := by
    dsimp only [w]
    rw [deriv_comp_affine (hv.differentiable (by norm_num))]
    simpa using hbneg
  have hE := varianceODEEnergy_nonpos_of_initial_deriv_neg hw hwpos hwsecond hwneg
  dsimp only [varianceODEEnergy,w] at hE
  rw [deriv_comp_affine (hv.differentiable (by norm_num))] at hE
  simpa [mul_pow,hb,sub_nonpos] using hE

end KLS.ConstantReduction
end
