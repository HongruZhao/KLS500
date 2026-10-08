import SpectralReductionCompleteSymmetrization
import SpectralReductionIndividualWindow

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

def completeGeometricWindow (M : ℝ) (q : ℕ) : ℝ :=
  ∑ i : Fin q, completeIntervalWeight q i*M^(i.rev : ℕ)

theorem completeGeometricWindow_succ (M : ℝ) (q : ℕ) :
    completeGeometricWindow M (q+1)=M*completeGeometricWindow M q+individualGeometricWindow M (q+1) := by
  unfold completeGeometricWindow individualGeometricWindow completeIntervalWeight
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.rev_castSucc,Fin.val_succ,Fin.rev_last,
    Fin.val_zero,pow_zero,mul_one,Fin.val_last]
  rw [Finset.mul_sum]
  have he : (∑ i : Fin q, ((i : ℕ)+1 : ℝ)*((q+1 : ℝ)-(i : ℕ))*M^((i.rev : ℕ)+1))=
      (∑ i : Fin q, M*(((i : ℕ)+1 : ℝ)*(q-(i : ℕ))*M^(i.rev : ℕ)))+
      ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^((i.rev : ℕ)+1) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  push_cast
  rw [he]
  ring

theorem completeGeometricWindow_identity (M : ℝ) (q : ℕ) :
    (M-1)^3*completeGeometricWindow M q =
      (q : ℝ)*M^(q+2)-(q+2 : ℝ)*M^(q+1)+(q+2 : ℝ)*M-q := by
  induction q with
  | zero => simp [completeGeometricWindow]
  | succ q ih =>
    rw [completeGeometricWindow_succ]
    have hW := individualGeometricWindow_identity M (q+1)
    push_cast at hW ⊢
    have he : (M-1)^3*(M*completeGeometricWindow M q+individualGeometricWindow M (q+1))=
        M*((M-1)^3*completeGeometricWindow M q)+(M-1)*((M-1)^2*individualGeometricWindow M (q+1)) := by ring
    rw [he,ih,hW]
    simp only [pow_succ]
    ring

end KLS.ConstantReduction
end
