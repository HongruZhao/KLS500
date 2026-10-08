import OptCubicBanach
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fin.VecNotation

noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def curryCubic (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] E →L[ℝ] ℝ) T.curryRight.curryRight

lemma curryCubic_apply (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (x y z : E) : curryCubic T x y z = T ![x,y,z] := by
  simp only [curryCubic, continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryRight_apply]
  congr 1
  funext i
  fin_cases i <;> simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cubic_vector_constant (x : E) : (![x,x,x] : Fin 3 → E) = fun _ => x := by
  funext i
  fin_cases i <;> rfl

theorem symmetric_cubic_multilinear_mixed_bound [FiniteDimensional ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (v ∘ σ) = T v)
    {C : ℝ} (hdiag : ∀ x : E, |T (fun _ => x)| ≤ C * ‖x‖^3)
    (x z : E) : |T ![x,x,z]| ≤ C * ‖x‖^2 * ‖z‖ := by
  have h12 : ∀ a b c, curryCubic T a b c = curryCubic T b a c := by
    intro a b c
    simp only [curryCubic_apply]
    have he : ((![b,a,c] : Fin 3 → E) ∘ Equiv.swap 0 1) = ![a,b,c] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [← he]
    exact hsym _ _
  have h23 : ∀ a b c, curryCubic T a b c = curryCubic T a c b := by
    intro a b c
    simp only [curryCubic_apply]
    have he : ((![a,c,b] : Fin 3 → E) ∘ Equiv.swap 1 2) = ![a,b,c] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [← he]
    exact hsym _ _
  have hd : ∀ a, |curryCubic T a a a| ≤ C * ‖a‖^3 := by
    intro a
    simpa only [curryCubic_apply,cubic_vector_constant] using hdiag a
  simpa only [curryCubic_apply] using symmetric_cubic_mixed_bound (curryCubic T) h12 h23 hd x z

theorem symmetric_cubic_multilinear_slice_norm_le [FiniteDimensional ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (v ∘ σ) = T v)
    {C : ℝ} (hC : 0 ≤ C) (hdiag : ∀ x : E, |T (fun _ => x)| ≤ C * ‖x‖^3)
    (x : E) : ‖curryCubic T x x‖ ≤ C * ‖x‖^2 := by
  apply (curryCubic T x x).opNorm_le_bound (by positivity)
  intro z
  simpa only [Real.norm_eq_abs,curryCubic_apply] using
    symmetric_cubic_multilinear_mixed_bound T hsym hdiag x z

end KLS.ConstantReduction
end
