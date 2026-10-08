import SpectralReductionIndividualSumRecurrence
import GeometricWindowArithmetic

/-! Exact weighted geometric windows from the individual insertion counts. -/
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

def individualGeometricWindow (M : ℝ) (q : ℕ) : ℝ :=
  ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)

theorem individualGeometricWindow_succ (M : ℝ) (q : ℕ) :
    individualGeometricWindow M (q+1) = M*individualGeometricWindow M q + (q+1 : ℝ) := by
  unfold individualGeometricWindow
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.rev_castSucc, Fin.val_succ, Fin.rev_last,
    Fin.val_zero, pow_zero, mul_one, Fin.val_last]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem individualGeometricWindow_identity (M : ℝ) (q : ℕ) :
    (M-1)^2*individualGeometricWindow M q = M^(q+1)-(q+1 : ℝ)*M+q := by
  induction q with
  | zero => simp [individualGeometricWindow]
  | succ q ih =>
    rw [individualGeometricWindow_succ]
    push_cast
    rw [show (M-1)^2*(M*individualGeometricWindow M q+(q+1)) =
      M*((M-1)^2*individualGeometricWindow M q)+(M-1)^2*(q+1) by ring, ih]
    rw [pow_succ]
    ring

theorem individual_geometric_window (q : ℕ) :
    (∑ i : Fin q, ((i : ℕ)+1 : ℝ)*(26/25 : ℝ)^(i.rev : ℕ)) =
      625*((26/25 : ℝ)^(q+1)-(q+1 : ℝ)*(26/25)+q) := by
  have hh := individualGeometricWindow_identity (26/25 : ℝ) q
  norm_num only [show ((26/25 : ℝ)-1)^2 = 1/625 by norm_num] at hh
  unfold individualGeometricWindow at hh
  linarith

end KLS.ConstantReduction
end
